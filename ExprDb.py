import z3
from pysmt.smtlib.parser import SmtLibParser, SmtLibCommand, SmtLibScript
from six.moves import cStringIO
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
import pysmt.solvers.z3 as pyz3

from pysmt.fnode import FNode, FNodeContent
from Z3Parser import Z3Parser
z3.set_param(proof = True)
z3.set_param(model = True)
class ExprDb:
    def __init__(self, filename):
        self.filename = filename
        self.parser = Z3Parser()

        self.converter = pyz3.Z3Converter(self.parser.env, z3.get_ctx(None))
        self.mgr = self.parser.env.formula_manager
        self._vars = {}
        self._pre2post = {}
        self._post2pre = {}
        self._solver_var = None #vsolver variable
        self._other_ass = [] #list of pysmt formula (Fnode)
        self._lvl_ass = {} #dict of z3 pysmt formula (Fnode)
        self._proxy_ass = {}
        self._chks = []
        self._cube = []
        self._active_lvl = 0
        self.populate_db(filename)
        self._predicate_name = None
        # print(self._lvl_ass)
    def __del__(self):
        print("del converter")
        del self.mgr
        del self.converter
    def _get_pre_post_name(self, name):
        if name.endswith("_0"):
            pre = name
            post = name[:-2]+"_n"
        elif name.endswith("_n"):
            pre = name[:-2]+"_0"
            post = name
        return pre, post

    def add_var(self, cmd):
        v, var_name, params, sort = cmd.args
        # print(v, var_name, params, sort)

        if var_name.endswith("_0") or var_name.endswith("_n"):
            pre, post = self._get_pre_post_name(var_name)
            zvar_pre = z3.Const(pre, self.converter._type_to_z3(sort))
            zvar_post = z3.Const(post, self.converter._type_to_z3(sort))
            self._vars[pre] = zvar_pre
            self._vars[post] = zvar_post
            self._pre2post[zvar_pre] = zvar_post
            self._post2pre[zvar_post] = zvar_pre
        elif "vsolver" in var_name:
            self._vars[var_name] = z3.Const(var_name, self.converter._type_to_z3(sort))
            self._solver = v
        else:
            self._vars[var_name] = z3.Const(var_name, self.converter._type_to_z3(sort))

    def post2pre(self):
        return self._post2pre

    def pre2post(self):
        return self._pre2post
    
    def get_vars(self):
        return self._vars

    def proxies_db(self):
        return self._proxy_ass

    def add_assert(self, command):
        if self._assert_contains(command, "proxy"):
            head, tail, _ = self._mk_assert_of(command, "proxy")
            self._proxy_ass[head] = tail
        elif self._assert_contains(command, "level"):
            head, tail, lvl = self._mk_assert_of(command, "level")
            if head in self._lvl_ass:


                self._lvl_ass[head].append((lvl, tail))
            else:
                self._lvl_ass[head] = [(lvl, tail)]

        else:
            self._other_ass.append(self.converter.convert(command.args[0]))

    def add_chk(self, command):
        self._chks.append(command.args)

    def get_proxies(self):
        return self._proxy_ass

    def get_lvls(self):
        return self._lvl_ass

    def get_others(self):
        return self._other_ass

    def get_chks(self):
        return self._chks

    def set_cube(self, cmd):
        print(cmd)
        print(cmd.args)
        
        lits = [self.converter.convert(v) for v in cmd.args.args()]
        self._cube = lits
         

    def get_cube(self):
        return self._cube

    def activate_lvl(self, cmd):
        lvl = cmd.args
        self._active_lvl = lvl

    def get_active_lvl(self):
        return self._active_lvl

    def _assert_contains(self, command, keyword):
        assert(len(command.args)==1 and command.name == "assert")
        for atom in command.args[0].get_atoms():
            if atom.is_symbol() and keyword in atom.symbol_name():
                return True
        return False

    def _negate(self, node):
        assert(len(node.args())<=1)
        if node.is_not():
            return node.arg(0)
        else:
            return self.mgr.Not(node)

    def _mk_assert_of(self, command, ass_type):
        lvl = None
        head, tail = self._filter_by_keyword(command.args[0].args(), ass_type)
        if "level" in str(head):
            lvl = int(str(head).split("!")[0].split("_")[1])
            print(lvl)
        assert(len(head)==1)
        head = self.converter.convert(self._negate(head[0]))
        tail = self.converter.convert(self.mgr.create_node(node_type = command.args[0].node_type(), args = tuple(tail),payload = None))
        return head, tail, lvl

    def _filter_by_keyword(self, nodes, keyword):
        contain_list = []
        not_contain_list = []
        for n in nodes:
            contain = False
            for atom in n.get_atoms():
                if atom.is_symbol() and keyword in atom.symbol_name():
                    contain = True
            if contain:
                contain_list.append(n)
            else:
                not_contain_list.append(n)
        return contain_list, not_contain_list

    def dump(self):
        print("VAR:")
        for k, v in self._vars.items():
            print(k, v)
        print("SOLVER:")
        print(self._solver)
        print("PROXIES:")
        for k, v in self._proxy_ass.items():
            print(k, "->", v)
        print("LVLS:")
        for k, v in self._lvl_ass.items():
            print(k, "->",  v)
        print("OTHERS:")
        for a in self._other_ass:
            print(a)
        print("CHECK-SAT:")
        for c in self._chks:
            print(c)

    def populate_db(self, filename):
        with open(filename, "r") as f:
            ori_query = f.readlines()
            for i in range(len(ori_query)):
                l = ori_query[i]
                if l.strip() == "(exit)":
                    break
            query_text = "".join(ori_query[:i])

            all_commands = self.parser.get_script(cStringIO(query_text)).commands

        for cmd in all_commands:
            if cmd.name=="declare-fun":
                self.add_var(cmd)
            elif cmd.name == "assert":
                self.add_assert(cmd)
            elif cmd.name == "check-sat":
                self.add_chk(cmd)
            elif cmd.name == "act-lvl":
                self.activate_lvl(cmd)
            elif cmd.name == "ind-gen":
                self.set_cube(cmd)
            else:
                print(cmd)

if __name__=="__main__":
    db = ExprDb("pool_solver_vsolver#0_1.smt2")
    
