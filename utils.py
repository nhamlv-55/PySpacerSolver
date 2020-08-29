from itertools import chain, combinations
from termcolor import colored
from Doping.pytorchtreelstm.treelstm import calculate_evaluation_orders
import z3
import json
import torch
import numpy as np
import os
import math
import matplotlib
import matplotlib.pyplot as plt
from matplotlib.pyplot import figure
from collections import defaultdict

CONST_EMB_SIZE = 6
MIN_COUNT = 5
def remap_keys(mapping):
    return [{str(k): v} for k, v in mapping.items()]

class MyError(Exception):
    def __init__(self, message, errors):

        # Call the base class constructor with the parameters it needs
        super().__init__(message)

        # Now for your custom code...
        self.errors = errors

def html_colored(text, color = "black"):
    text = text.replace("<", "&lt;")
    text = text.replace(">", "&gt;")
    return '<p><font size="4" face="monospace" color="%s">%s</font></p>'%(color, text)

def visualize(cube, inducted_cube, html_file = None):
    for l in cube:
        if l in inducted_cube:
            print(colored("||\t"+str(l), 'blue'))
            if html_file is not None:
                html_file.write(html_colored(str(l), 'blue'))
        else:
            print(colored("||\t"+str(l), 'red'))
            if html_file is not None:
                html_file.write(html_colored(str(l), 'red'))

def powerset(policy):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    return chain.from_iterable(combinations(policy, r) for r in range(len(policy)+1))

class HtmlVisPage:
    def __init__(self, filename):
        self.filename = filename
        self.header = '<!DOCTYPE html>\n<html>\n<body>\n'
        self.footer = '</body>\n</html>'
        self.body = []
    def write(self, s):
        self.body.append(s)

    def dump(self):
        with open(self.filename, "w") as f:
            f.write(self.header)
            f.writelines(self.body)
            f.write(self.footer)

class ConsEmb:
    """
    use the value of the the constant and put it into an appropriate bin
    """
    def __init__(self, emb_size):
        assert(emb_size%2==0)
        self.id2const = {}
        self.const2id = {}
        #each constant is in the range 10^-mag_range to 10^mag_range
        self.mag_range = int((emb_size - 2) / 2)
        self.normalized_val = None
    def add_const(self, const_node):
        '''add a const to vocab and return its id'''
        if const_node == 0:
            zero_emb = [0]*(2*self.mag_range + 2)
            zero_emb[self.mag_range]=1
            zero_emb[-1]=0.0
            return -1, zero_emb
        num = const_node.numerator_as_long()
        den = const_node.denominator_as_long()
        # sign = num >= 0
        val = float(num/den)
        # print(num)
        # print("------------------ = {}".format(val))
        # print(den)

        magnitude = int(math.log10(abs(val)))
        magnitude_vector = [0]*(2*self.mag_range + 1)
        magnitude_vector[self.mag_range+magnitude] = 1
        
        # print("magnitude", magnitude)
        sign = val/abs(val)
        norm_val = sign*math.log(abs(val))*(10**-magnitude)
        # norm_val = val*(10**-magnitude)
        # print(norm_val)
        return -1, magnitude_vector + [norm_val]

class LocalConsEmb:
    """
    randomized constant embedding
    """
    def __init__(self, emb_size):
        self.id2const = {}
        self.const2id = {}
        self.const_size = 0
        self.emb = np.random.normal(size=(100, emb_size))
    def add_const(self, const_node):
        '''add a const to vocab and return its id'''
        const = str(const_node)
        if const in self.const2id:
            idx = self.const2id[const]
            return idx, list(self.emb[idx])
        else:
            idx = self.const_size
            self.const2id[const] = idx
            self.id2const[idx] = const
            self.const_size+=1
            return idx, list(self.emb[idx])


class Vocab:
    def __init__(self):
        self.id2w = {}
        self.w2id = {}
        self.size = 0

        self.id2s = {}
        self.s2id = {}
        self.sort_size = 0

        #add constant
        for t in "<ROOT> <UNK> <NUMBER> + - * / <= >= = not".split():
            self.add_token(t)

        for s in "<ROOT> <UNK> Bool <VAR> <POS_RAT> <ZERO> <Real> <NEG_RAT> <BOOL_VAR>".split():
            self.add_sort(s)

        self.const_emb_size = 0
    def add_token(self, w):
        '''add a token to vocab and return its id'''
        if w in self.w2id:
            return self.w2id[w]
        else:
            idx = self.size
            self.w2id[w] = idx
            self.id2w[idx] = w
            self.size+=1
            return self.w2id[w]

    def add_sort(self, sort):
        '''add a sort to vocab and return its id'''
        if sort in self.s2id:
            return self.s2id[sort]
        else:
            idx = self.sort_size
            self.s2id[sort] = idx
            self.id2s[idx] = sort
            self.sort_size+=1
            return self.s2id[sort]

    def dump(self):
        print("ID2W:", self.id2w)
        print("W2ID:", self.w2id)

    def save(self, filename):
        vocab = {"id2w": self.id2w, "w2id": self.w2id,
                 "size": self.size,
                 "id2s": self.id2s, "s2id": self.s2id,
                 "sort_size": self.sort_size,
                 "const_emb_size": self.const_emb_size}
        with open(filename, "w") as f:
            json.dump(vocab, f)

    def load(self, filename):
        with open(filename, "r") as f:
            data = json.load(f)

        self.id2w = data["id2w"]
        self.w2id = data["w2id"]
        self.size = data["size"]
        self.id2s = data["id2s"]
        self.s2id = data["s2id"]
        self.sort_size = data["sort_size"]
        self.const_emb_size = data["const_emb_size"]

class Node:
    def __init__(self, const_emb_size):
        self._raw_expr = ""
        self._token = ""
        self._token_id = -1
        self._sort_id = -1
        self._children = list()
        self._sort = None
        self._const_emb = [0]*const_emb_size
        self._num_child = 0
        self._node_idx = -1
        
    def keys(self):
        return ["children", "index", "features"]

    def __getitem__(self, key):
        if key=="children": return self._children
        elif key =="index": return self._node_idx
        elif key =="features": return self.get_feat()
        elif key =="token_id": return self._token_id
    def __setitem__(self, key, value):
        if key=="children": return self.set_children(value)
        elif key =="index": return self.set_node_idx(value)

    def set_token(self, ast_node, vocab, local_emb = None):
        if z3.is_rational_value(ast_node):
            self._token = "<NUMBER>"
            if local_emb is not None:
                idx, emb_val = local_emb.add_const(ast_node)
                self._const_emb = emb_val
            self._token_id = vocab.add_token(self._token)
            self._raw_expr = str(ast_node)
        else:
            self._token = ast_node.decl().name()
            self._token_id = vocab.add_token(self._token)
            self._raw_expr = str(ast_node)

    def set_sort(self, ast_node, vocab):
        if z3.is_const(ast_node):
            if z3.is_bool(ast_node):
                sort = "<BOOL_VAR>"
            elif ast_node == 0:
                sort = "<ZERO>"
            elif z3.is_int(ast_node):
                if ast_node < 0:
                    sort = "<NEG_INT>"
                else:
                    sort = "<POS_INT>"
            elif z3.is_rational_value(ast_node):
                fl = float(ast_node.numerator_as_long())/float(ast_node.denominator_as_long())
                if fl < 0:
                    sort = "<NEG_RAT>"
                else:
                    sort = "<POS_RAT>"
            else:
                sort = "<VAR>"
        elif ast_node.decl().name() == "and":
            sort = "<AND>"
        else:
            sort = ast_node.sort().name()
        self._sort = sort
        self._sort_id = vocab.add_sort(self._sort)
    def set_node_idx(self, idx):
        self._node_idx = idx

    def get_node_idx(self):
        return self._node_idx

    def token(self):
        return self._token

    def sort(self):
        return self._sort

    def set_children(self, children):
        self._children = children
        self._num_child = len(children)

    def children(self):
        return self._children

    def set_as_root(self, vocab):
        self._token = "<ROOT>"
        self._token_id = vocab.add_token(self._token)
        self._raw_expr = "<ROOT>"
        self._sort = "<ROOT>"
        self._sort_id = vocab.add_sort(self._sort)

    def to_json(self):
        if self._num_child==0:
            return {"token": self._token, "token_id": self._token_id, "sort": self._sort, "sort_id": self._sort_id, "children": [], "expr": self._raw_expr, "features": self.get_feat()}
        else:
            return {"token": self._token, "token_id": self._token_id, "sort": self._sort, "sort_id": self._sort_id, "children": [child.to_json() for child in self._children], "expr": self._raw_expr, "features": self.get_feat()}

    def __str__(self):
        return json.dumps(self.to_json(), indent = 2)

    def rewrite(self, write_emb = True):
        if self._num_child==0:
            if write_emb:
                return "%s|%s|%s"%(self._token, self._sort, str(self._const_emb))
            else:
                return "%s|%s"%(self._token, self._sort)
        else:
            childs = [child.rewrite(write_emb) for child in self._children]
            childs = " ".join(childs)
            return "%s|%s (%s)"%(self._token, self._sort, childs)
            

    def get_feat(self):
        feat = [self._token_id, self._sort_id]
        feat.extend(self._const_emb)
        return feat

def ast_to_node(ast_node, vocab, local_const_emb):
    node = Node(vocab.const_emb_size)
    node.set_token(ast_node, vocab, local_const_emb)
    node.set_sort(ast_node, vocab)
    if ast_node.num_args == 0:
        return node
    else:
        node.set_children([ast_to_node(child, vocab, local_const_emb) for child in ast_node.children()])
        return node

def rootify(ast_node, vocab):
    '''
    attach the tree to a dummy node called ROOT to make sure everything is a tree (even a single node)
    '''
    root_node = Node(vocab.const_emb_size)
    root_node.set_as_root(vocab)
    root_node.set_children([ast_node])
    return root_node

def ast_to_tree(ast_node, vocab, local_const_emb):
    return rootify(ast_to_node(ast_node, vocab, local_const_emb), vocab)

def _label_node_index(node, n):
    node['index'] = n
    for child in node['children']:
        n += 1
        n = _label_node_index(child, n)
    return n

def _gather_node_attributes(node, key):
    if key in node.keys():
        features = [node[key]]
    for child in node['children']:
        features.extend(_gather_node_attributes(child, key))
    return features


def _gather_adjacency_list(node):
    adjacency_list = []
    for child in node['children']:
        adjacency_list.append([node['index'], child['index']])
        adjacency_list.extend(_gather_adjacency_list(child))

    return adjacency_list


def convert_tree_to_tensors(tree, device=torch.device('cuda')):
    # Label each node with its walk order to match nodes to feature tensor indexes
    # This modifies the original tree as a side effect
    n = 0
    n = _label_node_index(tree, n)
    features = _gather_node_attributes(tree, 'features')
    adjacency_list = _gather_adjacency_list(tree)

    # print("LEN FEATURES", len(features))
    # print("ADJ LIST", adjacency_list)
    node_order, edge_order = calculate_evaluation_orders(adjacency_list, len(features))

    return {
        'features': torch.tensor(features, device=device, dtype=torch.float),
        'node_order': torch.tensor(node_order, device=device, dtype=torch.int64),
        'adjacency_list': torch.tensor(adjacency_list, device=device, dtype=torch.int64),
        'edge_order': torch.tensor(edge_order, device=device, dtype=torch.int64),
    }

class Dataset:
    def __init__(self, checkpoint = 500, const_emb_size = CONST_EMB_SIZE, folder = None, html_vis_page = None, small_test = False):
        self.vocab = Vocab()
        self.dataset = {}
        if html_vis_page is not None:
            self.html_vis_page = HtmlVisPage(html_vis_page)
        else:
            self.html_vis_page = None
        #checkpoint: save the vocab after each n datapoints
        self.checkpoint = checkpoint
        self.folder = folder

        #const emb size
        self.const_emb_size = const_emb_size
        self.vocab.const_emb_size = const_emb_size
        #data for constructing matrix X
        self.positive_lit = {}
        self.positive_X = defaultdict(int)
        self.positive_lit_count = defaultdict(int)

        self.negative_lit = {}
        self.negative_X = defaultdict(int)
        self.all_pair_count = defaultdict(int)
        self.negative_lit_count = defaultdict(int)
        #a counter to dump X.1.json, X.2.json, etc.
        self.X_counter = 0
        self.save_every = 10

        self.small_test = small_test #a flag to print extra verbose

    def print2html(self, s, color = "black"):
        print(s)
        if self.html_vis_page is not None:
            self.html_vis_page.write(html_colored(s, color))


    def normalize(self, ast):
        return z3.simplify(ast, arith_ineq_lhs = True, sort_sums = True)

    def normalize_cube(self, cube):
        new_cube = []
        for l in cube:
            new_cube.append(self.normalize(l))
        return new_cube

    # def check_lit_conflict(self, cube, inducted_cube, local_const_emb):
    #     '''
    #     Check if exists 2 lits that are the same after tokenization, but one is red and one is blue.
    #     Also returns a list of trees. Each tree is a conversion of a literal in the cube.
    #     '''
    #     self.print2html("Checking for lit conflict")
        
    #     #a set contain all the lits that stays after ind_gen
    #     conflict = False
    #     blue_trees = set()
    #     red_trees = set()
    #     all_lit_trees = []
    #     for lit in cube:
    #         lit_tree = ast_to_tree(lit, self.vocab, local_const_emb)
    #         all_lit_trees.append(lit_tree)
    #         if lit in inducted_cube:
    #             blue_trees.add(lit_tree.rewrite())
    #         else:
    #             red_trees.add(lit_tree.rewrite())

    #     for i in range(len(cube)):
    #         lit = cube[i]
    #         lit_tree = all_lit_trees[i].rewrite()
    #         if lit in inducted_cube and lit_tree not in red_trees:
    #             self.print2html("%s =====> %s"%(lit, lit_tree), "blue")
    #         elif lit in inducted_cube and lit_tree in red_trees:
    #             conflict = True
    #             self.print2html("%s =====> %s"%(lit, lit_tree), "purple")
    #         elif lit not in inducted_cube and lit_tree in blue_trees:
    #             conflict = True
    #             self.print2html("%s =====> %s"%(lit, lit_tree), "purple")
    #         elif lit not in inducted_cube and lit_tree not in blue_trees:
    #             self.print2html("%s =====> %s"%(lit, lit_tree), "red")

    #     self.print2html("----------------------------")
    #     return conflict, all_lit_trees

    # def add_dp(self, cube, inducted_cube, filename):
    #     if len(self.dataset)%self.checkpoint==0:
    #         self.save_vocab(self.folder)
    #     local_const_emb = LocalConsEmb()
    #     if len(cube)<=1:
    #         return
    #     #Normalize before doing anything
    #     self.print2html("normalize the cube")

    #     self.print2html("raw cube")
    #     visualize(cube, inducted_cube, self.html_vis_page)

    #     self.print2html("normalized cube")
    #     cube = self.normalize_cube(cube)
    #     inducted_cube = self.normalize_cube(inducted_cube)
    #     visualize(cube, inducted_cube, self.html_vis_page)

    #     #Check for conflict
    #     conflict, all_lit_trees = self.check_lit_conflict(cube, inducted_cube, local_const_emb)
    #     if conflict:
    #         self.print2html("There is a self-conflict. Drop this cube")
    #         return



    #     last_collision_file = None

    #     #TODO: manually construct C_tree based on all L_tree (should save half the time)
    #     C_tree = ast_to_tree(z3.And(cube), self.vocab, local_const_emb)
    #     for i in range(len(cube)):

    #         for j in range(i+1, len(cube)):
    #             '''4 possible labels: both lits are dropped 0, only one is dropped 1, non is dropped 2'''
    #             if cube[i] in inducted_cube and cube[j] in inducted_cube:
    #                 label = 0
    #             elif cube[i] not in inducted_cube and cube[j] not in inducted_cube:
    #                 label = 0
    #             else:
    #                 label = 1

    #             L_a_tree = all_lit_trees[i]
    #             L_b_tree = all_lit_trees[j]

    #             dp_filename = filename+ "."+ str(i)+ "."+ str(j)+ ".dp.json"
    #             X = (C_tree.rewrite(), L_a_tree.rewrite(), L_b_tree.rewrite())
    #             datapoint = {"filename": filename, "cube": cube, "inducted_cube": inducted_cube, "label": label}

    #             if X in self.dataset and self.dataset[X]["label"]!=label:
    #                 if last_collision_file is None:
    #                     self.print2html("Exist a same datapoint with a different label")
    #                     self.print2html("PREVIOUS ENTRY")
    #                     self.print2html(self.dataset[X]["filename"])
    #                     visualize(self.dataset[X]["cube"], self.dataset[X]["inducted_cube"], self.html_vis_page)
    #                     self.print2html("THIS ENTRY")
    #                     self.print2html(filename)
    #                     visualize(cube, inducted_cube, self.html_vis_page)
    #                     last_collision_file = self.dataset[X]["filename"]
    #             else:
    #                 self.dataset[X] = datapoint
    #             with open(dp_filename, "w") as f:
    #                 json.dump({"C_tree": C_tree.to_json(), "L_a_tree": L_a_tree.to_json(), "L_b_tree": L_b_tree.to_json(), "label": label}, f)

    def parse_cube_to_lit_jsons(self, cube):
        """
        Given a cube, parse and return the JSON tree of its lits
        """
        #Normalize before doing anything
        local_const_emb = ConsEmb(emb_size = self.const_emb_size)
        
        cube = self.normalize_cube(cube)
        results = []

        for lit in cube:
            L_tree = ast_to_tree(lit, self.vocab, local_const_emb)
            
            L_json = {"tree": L_tree.to_json()}
            results.append(L_json)

        return results

    def add_dual_dp_to_X(self, ori_cube, inducted_cube, folder):
        """
        Like add_dp_to_X, but take into account the original cube as well
        """
        self.add_dp_to_positive_X(inducted_cube, folder)
        self.add_dp_to_negative_X(ori_cube, inducted_cube, folder)

    def add_dp_to_negative_X(self, ori_cube, inducted_cube, folder):
        """
        Build the negative X matrix. Require both the ori_cube and the inducted_cube
        P(lit_x is drop| lit_y is kept) = how many times (x not in inducted cube, (x,y) in ori cube)/how many times (x,y) in ori cube
        """
        #Normalize before doing anything
        ori_cube = self.normalize_cube(ori_cube)
        inducted_cube = self.normalize_cube(inducted_cube)
        print("ori_cube", ori_cube)
        print("inducted_cube", inducted_cube)
        local_const_emb = ConsEmb(emb_size = self.const_emb_size)

        
        L_ori_trees_str = []
        L_inducted_trees_str = []
        #update L_freq and L
        for i in range(len(ori_cube)):
            L_a_tree = ast_to_tree(ori_cube[i], self.vocab, local_const_emb)
            L_a_tree_str = str(ori_cube[i])
            L_ori_trees_str.append(L_a_tree_str)

            if L_a_tree_str not in self.negative_lit:
                a_index = len(self.negative_lit)
                with open(os.path.join(folder, "negative_lit_" + str(a_index)+".json"), "w") as f:
                    json.dump({"index": a_index, "tree": L_a_tree.to_json()}, f)

                self.negative_lit[L_a_tree_str]=a_index
            self.negative_lit_count[L_a_tree_str] += 1

        #update all pair count
        for i in range(len(ori_cube)):
            for j in range(i, len(ori_cube)):
                L_i_tree_str = str(ori_cube[i])
                L_j_tree_str = str(ori_cube[j])

                i_index = self.negative_lit[L_i_tree_str]
                j_index = self.negative_lit[L_j_tree_str]
                self.all_pair_count[(i_index, j_index)]+=1
                self.all_pair_count[(j_index, i_index)]+=1



        #build L_inducted_trees_str
        for i in range(len(inducted_cube)):
            L_a_tree = ast_to_tree(inducted_cube[i], self.vocab, local_const_emb)
            L_a_tree_str = str(inducted_cube[i])

            if self.small_test:
                print(L_a_tree_str)
                print(L_a_tree_str in L_ori_trees_str)
            L_inducted_trees_str.append(L_a_tree_str)

        if self.small_test:
            print("L_ori_trees")
            print("\n".join(L_ori_trees_str))
            print("L_inducted_trees")
            print("\n".join(L_inducted_trees_str))

        #collect anti-occurance
        for ori_lit_idx in range(len(ori_cube)):
            L_ori_tree_str = L_ori_trees_str[ori_lit_idx]
            ori_lit_global_idx = self.negative_lit[L_ori_tree_str]
            if L_ori_tree_str not in L_inducted_trees_str:
                #mark all pair into the negative_X matrix
                for inducted_lit_idx in range(len(inducted_cube)):
                    L_inducted_tree_str = L_inducted_trees_str[inducted_lit_idx]
                    inducted_lit_global_idx = self.negative_lit[L_inducted_tree_str]

                    self.negative_X[(ori_lit_global_idx, inducted_lit_global_idx)]+=1



    def add_dp_to_positive_X(self, inducted_cube, folder):
        """
        Build the X matrix. Only the inducted cube is needed
        """
        #if the cube has only 1 lit, skip it
        if len(inducted_cube)==1:
            return
        #Normalize before doing anything
        inducted_cube = self.normalize_cube(inducted_cube)
        local_const_emb = ConsEmb(emb_size = self.const_emb_size)
        
        #build all L_a_tree and L_a_tree_str
        L_trees_str = []

        for i in range(len(inducted_cube)):
            L_a_tree = ast_to_tree(inducted_cube[i], self.vocab, local_const_emb)
            L_a_tree_str = str(inducted_cube[i])
            L_trees_str.append(L_a_tree_str)

            if L_a_tree_str not in self.positive_lit:
                a_index = len(self.positive_lit)
                self.positive_lit[L_a_tree_str]=a_index
                with open(os.path.join(folder, "positive_lit_" + str(a_index)+".json"), "w") as f:
                    json.dump({"index": a_index, "tree": L_a_tree.to_json()}, f)

            #update L_freq: how many times a literal appears in the whole dataset
            self.positive_lit_count[L_a_tree_str] += 1

        #collect co-occurance
        for i in range(len(inducted_cube)):
            for j in range(i+1, len(inducted_cube)):
                L_a_tree_str = str(L_trees_str[i])
                L_b_tree_str = str(L_trees_str[j])

                a_index = self.positive_lit[L_a_tree_str]
                b_index = self.positive_lit[L_b_tree_str]

                self.positive_X[(a_index, b_index)]+=1
                self.positive_X[(b_index, a_index)]+=1

    def save_vocab(self, folder):
        print("SAVING VOCAB")
        self.vocab.save(os.path.join(folder, "vocab.json"))

    def save_X_L(self, folder, print_matrix = False, forced = False):
        #if forced, save the dataset regardless of X_counter
        if forced == False and self.X_counter%self.save_every !=1:
            self.X_counter+=1
            return

        assert(self.positive_lit.keys()==self.positive_lit_count.keys())
        assert(self.negative_lit.keys()==self.negative_lit_count.keys())
        self.X_counter+=1

        if forced:
            all_lits_set = set(self.negative_lit.keys())
            inducted_lits_set = set(self.positive_lit.keys())
            diff_set = set(all_lits_set.difference(inducted_lits_set))

            print("all_lits_set", len(all_lits_set))
            print("inducted_lits_set", len(inducted_lits_set))
            print("diff", len(all_lits_set.difference(inducted_lits_set)))
            diff_dict = {}
            for lit in diff_set:
                diff_dict[lit] = self.negative_lit_count[lit]
            with open(os.path.join(folder, "diff_set.json"), "w") as f:
                json.dump(diff_dict, f)
            all_cooc_set = set(self.positive_X.keys())
            all_antioc_set = set(self.negative_X.keys())
            intersect_set = all_cooc_set.intersection(all_antioc_set)
            print(len(all_cooc_set), len(all_antioc_set), len(intersect_set))
            with open(os.path.join(folder, "intersect_set.json"), "w") as f:
                for lit in intersect_set:
                    f.write("{}\n".format(lit))

                    

        with open(os.path.join(folder, "positive_lits_map" + str(self.X_counter).zfill(5)+ ".json"), "w") as f:
            json.dump(self.positive_lit, f)
        with open(os.path.join(folder, "positive_lits_count" + str(self.X_counter).zfill(5)+ ".json"), "w") as f:
            json.dump(self.positive_lit_count, f)
        with open(os.path.join(folder, "negative_lits_map" + str(self.X_counter).zfill(5)+ ".json"), "w") as f:
            json.dump(self.negative_lit, f)
        with open(os.path.join(folder, "negative_lits_count" + str(self.X_counter).zfill(5)+ ".json"), "w") as f:
            json.dump(self.negative_lit_count, f)
        positive_X_matrix = np.zeros((len(self.positive_lit), len(self.positive_lit)))
        for k in self.positive_X:
            i,j = k
            if self.small_test:
                print("positive pair:", k, self.positive_X[k])
            positive_X_matrix[i][j] = self.positive_X[k]

        negative_X_matrix = np.zeros((len(self.negative_lit), len(self.negative_lit)))
        for k in self.negative_X:
            i,j = k
            if self.small_test:
                print("negative pair:", k, self.negative_X[k])
            negative_X_matrix[i][j] = self.negative_X[k]

        all_pair_matrix = np.zeros((len(self.negative_lit), len(self.negative_lit)))
        for k in self.all_pair_count:
            i,j=k
            all_pair_matrix[i][j] = self.all_pair_count[k]

        P_negative_matrix = np.zeros((len(self.negative_lit), len(self.negative_lit)))
        for i in range(len(self.negative_lit)):
            for j in range(len(self.negative_lit)):
                if negative_X_matrix[i][j]==0:
                    P_negative_matrix[i][j]=0
                elif all_pair_matrix[i][j]<MIN_COUNT:
                    P_negative_matrix[i][j]=0
                else:
                    P_negative_matrix[i][j] = negative_X_matrix[i][j]/all_pair_matrix[i][j]
        # P_negative_matrix = np.divide(negative_X_matrix, all_pair_matrix)
        with open(os.path.join(folder, "positive_X_" + str(self.X_counter).zfill(5)+ ".json"), "w") as f:
            json.dump({"X": positive_X_matrix.tolist(), "X_raw": remap_keys(self.positive_X)}, f)
        with open(os.path.join(folder, "negative_X_" + str(self.X_counter).zfill(5)+ ".json"), "w") as f:
            json.dump({"X": negative_X_matrix.tolist(), "X_raw": remap_keys(self.negative_X)}, f)
        with open(os.path.join(folder, "all_pairs_X_" + str(self.X_counter).zfill(5)+ ".json"), "w") as f:
            json.dump({"X": all_pair_matrix.tolist()}, f)
        with open(os.path.join(folder, "P_negative_X_matrix_" + str(self.X_counter).zfill(5)+ ".json"), "w") as f:
            json.dump({"X": P_negative_matrix.tolist()}, f)





        if print_matrix:
            fig, axs = plt.subplots(4, 1, figsize = (20, 20))
            im = axs[0].imshow(positive_X_matrix, interpolation = None)
            im = axs[1].imshow(positive_X_matrix.astype(bool), interpolation = None)
            im = axs[2].imshow(negative_X_matrix, interpolation = None)
            im = axs[3].imshow(negative_X_matrix.astype(bool), interpolation = None)
            plt.savefig("XP.svg")
        


    def dump_dataset(self, folder):
        pass
        print("DUMPING DATASET IN TOKEN FORMAT")
        with open(os.path.join(folder, "ds_token_form.json"), "w") as f:
            json.dump(self.dataset, f, indent = 2)

    def dump_html(self):
        if self.html_vis_page is not None:
            self.html_vis_page.dump()
