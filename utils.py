from itertools import chain, combinations
from termcolor import colored
from Doping.pytorchtreelstm.treelstm import calculate_evaluation_orders
import z3
import json
import torch
import numpy as np
import os

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
    def __init__(self, emb_size = 30):
        self.id2const = {}
        self.const2id = {}
        self.const_size = 0
        self.emb = np.random.normal(size=(100, emb_size))
    def add_const(self, const):
        '''add a const to vocab and return its id'''
        if const in self.const2id:
            idx = self.const2id[const]
            return idx, list(self.emb[idx])
        else:
            idx = self.const_size
            self.const2id[const] = idx
            self.id2const[idx] = const
            self.const_size+=1
            return idx, list(self.emb[idx])

class LocalConsEmb:
    def __init__(self, emb_size = 30):
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
        self.add_token("<ROOT>")
        self.add_token("<UNK>")

        self.add_sort("<ROOT>")
        self.add_sort("<UNK>")

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
        vocab = {"id2w": self.id2w, "w2id": self.w2id, "size": self.size, "id2s": self.id2s, "s2id": self.s2id, "sort_size": self.sort_size}
        with open(filename, "w") as f:
            json.dump(vocab, f)
class Node:
    def __init__(self):
        self._raw_expr = ""
        self._token = ""
        self._token_id = -1
        self._sort_id = -1
        self._children = list()
        self._sort = None
        self._const_emb = [0]*30
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
                return "%s|%s|%s"%(self._token, self._sort, str(self._const_emb[:5]))
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
    node = Node()
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
    root_node = Node()
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
        'features': torch.tensor(features, device=device, dtype=torch.int64),
        'node_order': torch.tensor(node_order, device=device, dtype=torch.int64),
        'adjacency_list': torch.tensor(adjacency_list, device=device, dtype=torch.int64),
        'edge_order': torch.tensor(edge_order, device=device, dtype=torch.int64),
    }

class Dataset:
    def __init__(self, checkpoint = 500, folder = None, html_vis_page = None):
        self.vocab = Vocab()
        self.dataset = {}
        if html_vis_page is not None:
            self.html_vis_page = HtmlVisPage(html_vis_page)
        else:
            self.html_vis_page = None
        #checkpoint: save the vocab after each n datapoints
        self.checkpoint = checkpoint
        self.folder = folder

        #data for constructing matrix X
        self.L = {}
        self.X = {}
        #a counter to dump X.1.json, X.2.json, etc.
        self.X_counter = 0
        self.save_every = 10

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

    def check_lit_conflict(self, cube, inducted_cube, local_const_emb):
        '''
        Check if exists 2 lits that are the same after tokenization, but one is red and one is blue.
        Also returns a list of trees. Each tree is a conversion of a literal in the cube.
        '''
        self.print2html("Checking for lit conflict")
        
        #a set contain all the lits that stays after ind_gen
        conflict = False
        blue_trees = set()
        red_trees = set()
        all_lit_trees = []
        for lit in cube:
            lit_tree = ast_to_tree(lit, self.vocab, local_const_emb)
            all_lit_trees.append(lit_tree)
            if lit in inducted_cube:
                blue_trees.add(lit_tree.rewrite())
            else:
                red_trees.add(lit_tree.rewrite())

        for i in range(len(cube)):
            lit = cube[i]
            lit_tree = all_lit_trees[i].rewrite()
            if lit in inducted_cube and lit_tree not in red_trees:
                self.print2html("%s =====> %s"%(lit, lit_tree), "blue")
            elif lit in inducted_cube and lit_tree in red_trees:
                conflict = True
                self.print2html("%s =====> %s"%(lit, lit_tree), "purple")
            elif lit not in inducted_cube and lit_tree in blue_trees:
                conflict = True
                self.print2html("%s =====> %s"%(lit, lit_tree), "purple")
            elif lit not in inducted_cube and lit_tree not in blue_trees:
                self.print2html("%s =====> %s"%(lit, lit_tree), "red")

        self.print2html("----------------------------")
        return conflict, all_lit_trees

    def add_dp(self, cube, inducted_cube, filename):
        if len(self.dataset)%self.checkpoint==0:
            self.save_vocab(self.folder)
        local_const_emb = LocalConsEmb()
        if len(cube)<=1:
            return
        #Normalize before doing anything
        self.print2html("normalize the cube")

        self.print2html("raw cube")
        visualize(cube, inducted_cube, self.html_vis_page)

        self.print2html("normalized cube")
        cube = self.normalize_cube(cube)
        inducted_cube = self.normalize_cube(inducted_cube)
        visualize(cube, inducted_cube, self.html_vis_page)

        #Check for conflict
        conflict, all_lit_trees = self.check_lit_conflict(cube, inducted_cube, local_const_emb)
        if conflict:
            self.print2html("There is a self-conflict. Drop this cube")
            return



        last_collision_file = None

        #TODO: manually construct C_tree based on all L_tree (should save half the time)
        C_tree = ast_to_tree(z3.And(cube), self.vocab, local_const_emb)
        for i in range(len(cube)):

            for j in range(i+1, len(cube)):
                '''4 possible labels: both lits are dropped 0, only one is dropped 1, non is dropped 2'''
                if cube[i] in inducted_cube and cube[j] in inducted_cube:
                    label = 0
                elif cube[i] not in inducted_cube and cube[j] not in inducted_cube:
                    label = 0
                else:
                    label = 1

                L_a_tree = all_lit_trees[i]
                L_b_tree = all_lit_trees[j]

                dp_filename = filename+ "."+ str(i)+ "."+ str(j)+ ".dp.json"
                X = (C_tree.rewrite(), L_a_tree.rewrite(), L_b_tree.rewrite())
                datapoint = {"filename": filename, "cube": cube, "inducted_cube": inducted_cube, "label": label}

                if X in self.dataset and self.dataset[X]["label"]!=label:
                    if last_collision_file is None:
                        self.print2html("Exist a same datapoint with a different label")
                        self.print2html("PREVIOUS ENTRY")
                        self.print2html(self.dataset[X]["filename"])
                        visualize(self.dataset[X]["cube"], self.dataset[X]["inducted_cube"], self.html_vis_page)
                        self.print2html("THIS ENTRY")
                        self.print2html(filename)
                        visualize(cube, inducted_cube, self.html_vis_page)
                        last_collision_file = self.dataset[X]["filename"]
                else:
                    self.dataset[X] = datapoint
                with open(dp_filename, "w") as f:
                    json.dump({"C_tree": C_tree.to_json(), "L_a_tree": L_a_tree.to_json(), "L_b_tree": L_b_tree.to_json(), "label": label}, f)


    def add_dp_to_X(self, inducted_cube, filename):
        """
        Build the X matrix. Only the inducted cube is needed
        """
        #Normalize before doing anything
        inducted_cube = self.normalize_cube(inducted_cube)
        local_const_emb = LocalConsEmb()
        folder = os.path.dirname(filename)
        for i in range(len(inducted_cube)):
            for j in range(i+1, len(inducted_cube)):
                L_a_tree = ast_to_tree(inducted_cube[i], self.vocab, local_const_emb)
                L_b_tree = ast_to_tree(inducted_cube[j], self.vocab, local_const_emb)

                L_a_tree_str = L_a_tree.rewrite(write_emb = False)
                L_b_tree_str = L_b_tree.rewrite(write_emb = False)

                if L_a_tree_str not in self.L:
                    a_index = len(self.L)
                    self.L[L_a_tree_str]=a_index
                    with open(os.path.join(folder, "lit_" + str(a_index)+".json"), "w") as f:
                        json.dump({"index": a_index, "tree": L_a_tree.to_json()}, f)
                if L_b_tree_str not in self.L:
                    b_index = len(self.L)
                    self.L[L_b_tree_str]=b_index
                    with open(os.path.join(folder, "lit_" + str(b_index)+".json"), "w") as f:
                        json.dump({"index": b_index, "tree": L_b_tree.to_json()}, f)
                a_index = self.L[L_a_tree_str]
                b_index = self.L[L_b_tree_str]

                if (a_index, b_index) in self.X:
                    self.X[(a_index, b_index)]+=1
                    self.X[(b_index, a_index)]+=1
                else:
                    self.X[(a_index, b_index)]=1
                    self.X[(b_index, a_index)]=1

    def save_vocab(self, folder):
        print("SAVING VOCAB")
        self.vocab.save(os.path.join(folder, "vocab.json"))

    def save_X_L(self, folder, forced = False):
        #if forced, save the dataset regardless of X_counter
        if forced == False and self.X_counter%self.save_every !=1:
            self.X_counter+=1
            return


        with open(os.path.join(folder, "L.json"), "w") as L_file:
            json.dump(self.L, L_file)

        print(len(self.L))
        print(len(self.X))

        X_matrix = np.zeros((len(self.L), len(self.L)))
        for k in self.X:
            i,j = k
            X_matrix[i][j] = self.X[k]

        for row in X_matrix:
            print(row)

        #calculating P
        #P[i][j] = P(j|i)
        P_matrix = np.zeros((len(self.L), len(self.L)))
        for i in range(len(self.L)):
            X_i = np.sum(X_matrix[i])
            for j in range(len(self.L)):
                if X_matrix[i][j]==0:
                    P_matrix[i][j]=0
                else:
                    P_matrix[i][j] = X_matrix[i][j]/X_i
        for row in P_matrix:
            print(row)

        
        
        with open(os.path.join(folder, "X" + str(self.X_counter).zfill(5)+ ".json"), "w") as X_file:
            json.dump({"X": X_matrix.tolist()}, X_file)
        with open(os.path.join(folder, "P" + str(self.X_counter).zfill(5)+ ".json"), "w") as P_file:
            json.dump({"P": P_matrix.tolist()}, P_file)


        self.X_counter+=1


    def dump_dataset(self, folder):
        pass
        print("DUMPING DATASET IN TOKEN FORMAT")
        with open(os.path.join(folder, "ds_token_form.json"), "w") as f:
            json.dump(self.dataset, f, indent = 2)

    def dump_html(self):
        if self.html_vis_page is not None:
            self.html_vis_page.dump()
