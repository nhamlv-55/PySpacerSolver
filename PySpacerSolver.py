import z3
from pysmt.smtlib.parser import SmtLibParser, SmtLibCommand, SmtLibScript
from six.moves import cStringIO
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
import pysmt.solvers.z3 as pyz3

from pysmt.fnode import FNode, FNodeContent
from Z3Parser import Z3Parser
z3.set_param(proof = True)
z3.set_param(model = True)
parser = Z3Parser()

converter = pyz3.Z3Converter(parser.env, z3.get_ctx(None))
mgr = parser.env.formula_manager
class PySpacerSolver:
    def __init__(self):
        self.solver = None
        self._vars = {}
        self._pre2post = {}
        self._post2pre = {}
        self._solver = None #vsolver variable
        self._other_ass = [] #list of pysmt formula (Fnode)
        self._level_ass = {} #dict of z3 pysmt formula (Fnode)
        self._proxy_ass = {}
        self._chks = []

    def _get_pre_post_name(self, name):
        if name.endswith("_0"):
            pre = name
            post = name[:-2]+"_n"
        elif name.endswith("_n"):
            pre = name[:-2]+"_0"
            post = name
        return pre, post


    def add_var(self, command):
        v, var_name, params, sort = cmd.args
        # print(v, var_name, params, sort)

        if var_name.endswith("_0") or var_name.endswith("_n"):
            pre, post = self._get_pre_post_name(var_name)
            zvar_pre = z3.Const(pre, converter._type_to_z3(sort))
            zvar_post = z3.Const(post, converter._type_to_z3(sort))
            self._vars[pre] = zvar_pre
            self._vars[post] = zvar_post
            self._pre2post[zvar_pre] = zvar_post
            self._post2pre[zvar_post] = zvar_pre
        elif "vsolver" in var_name:
            self._vars[var_name] = z3.Const(var_name, converter._type_to_z3(sort))
            self._solver = v
        else:
            self._vars[var_name] = z3.Const(var_name, converter._type_to_z3(sort))

    def get_vars(self):
        return self._vars

    def add_assert(self, command):
        if self._assert_contains(command, "proxy"):
            head, tail = self._mk_assert_of(command, "proxy")
            self._proxy_ass[str(head)] = {"head":head, "tail": tail, "cmd": command.args[0]}
        elif self._assert_contains(command, "level"):
            head, tail = self._mk_assert_of(command, "level")
            self._level_ass[str(head)] = {"head": head, "tail":tail, "cmd": command.args[0]}
        else:
            self._other_ass.append(command.args[0])

    def add_chk(self, command):
        self._chks.append(command.args)

    def get_proxies(self):
        return self._proxy_ass

    def get_levels(self):
        return self._level_ass

    def get_others(self):
        return self._other_ass

    def get_chks(self):
        return self._chks

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
            return mgr.Not(node)

    def _mk_assert_of(self, command, ass_type):
        head, tail = self._filter_by_keyword(command.args[0].args(), ass_type)
        assert(len(head)==1)
        head = self._negate(head[0])
        tail = mgr.create_node(node_type = command.args[0].node_type(), args = tuple(tail),payload = None)
        return head, tail
    
    def check(self, levels = None, lemma = None):
        self.solver = z3.Solver()

        # add constraints to solver
        for l in levels:
            solver.add(converter.convert(self._level_ass[l]))

        for lit in lemma:
            solver.add(lit)

        # run solver
        res = self.solver.check()
        # extract model or proof
        answer = None
        if res == z3.sat:
            answer = self.solver.model()
        elif res == z3.unsat:
            answer = self.solver.proof()

        print("RES", res)
        print("ANS", answer)
        return res, answer

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
        print("LEVELS:")
        for k, v in self._level_ass.items():
            print(k, "->",  v)
        print("OTHERS:")
        for a in self._other_ass:
            print(a)
        print("CHECK-SAT:")
        for c in self._chks:
            print(c)
filename = "/home/nv3le/workspace/saturation-visualization/deepSpacer/pobvis/app/pool_solver_vsolver#0_12.smt2"

if __name__=="__main__":
    
    s = PySpacerSolver()
    with open(filename, "r") as f:
        ori_query = f.readlines()
        for i in range(len(ori_query)):
            l = ori_query[i]
            if l.strip() == "(exit)":
                break
        query_text = "".join(ori_query[:i])

        all_commands = parser.get_script(cStringIO(query_text)).commands
    

    for cmd in all_commands:
        if cmd.name=="declare-fun":
            s.add_var(cmd)
        elif cmd.name == "assert":
            s.add_assert(cmd)
        elif cmd.name == "check-sat":
            s.add_chk(cmd)
    
    
    s.dump()
