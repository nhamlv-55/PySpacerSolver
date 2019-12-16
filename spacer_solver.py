from ExprDb import ExprDb
import z3
class SpacerSolverProxyDb(object):
    def __init__(self, proxies_db):
        #map from proxy_lit to expr. Note that there maybe duplicated exprs
        self._proxies_db = proxies_db
    def size(self):
        return len(self._proxies_db)

    def find(self, proxy_lit):
        return self._proxies_db[proxy_lit]

    def find_expr(self, e):
        for (p,expr) in self._proxies_db.items():
            if e== expr:
                return p
        return None

    def add(self, e):
        # print("CURRENT SIZE", self.size())
        """Adds proxy and returns its literal"""
        new_lit = self.find_expr(e)
        if new_lit is not None:
            return new_lit
        else:
            new_lit = z3.Const("spacer_proxy!%s"%str(self.size()), z3.BoolSort())
            self._proxies_db[new_lit] = e
            return new_lit

    def dump(self):
        print("SIZE:", self.size())
        for (k,v) in self._proxies_db.items():
            print(k, "<-", v)

    def push(self):
        pass
    def pop(self):
        pass

class SpacerSolver(object):
    def __init__(self, zsolver, proxies_db):
        self._zsolver = zsolver
        self._levels = []
        self._proxies_db = SpacerSolverProxyDb(proxies_db)
        self._active_level = None
    def add(self, e):
        """Add background assertion to the solver"""
        self._zsolver.add(e)

    def add_proxy(self, e):
        """Adds an assertion guarded by a Boolean literal and rerturns it"""
        # XXX if e is already a proxy return
        # XXX if e is a Bool constant return e and don't create a proxy
        proxy_lit = self._proxies_db.add(e)
        self._zsolver.add(z3.Implies(proxy_lit, e))
        # print("ADDING:", e, "<-", proxy_lit)
        return proxy_lit

    def get_proxy(self, lit):
        return self._proxies_db.find(lit)
    def add_leveled(self, lvl, e):
        """Add an assertion at a specified level"""
        self.ensure_level(lvl)
        level_lit = self._mk_level_lit(lvl)
        self._zsolver.add(z3.Implies(level_lit, e))

    def ensure_level(self, lvl):
        """Ensure that solver has lvl number of levels"""
        while (len(self._levels) < lvl):
            self._levels.append(self._mk_level_lit(len(self._levels)))

    def _mk_level_lit(self, lvl):
        if lvl < len(self._levels):
            return self._levels[lvl]

        lit = z3.Bool("level#{}".format(lvl))
        return z3.Not(lit)

    def activate_level(self, lvl):
        """Activate specified level"""
        self._active_level = lvl

    def get_active_level(self):
        """Return currently active level"""
        return self._active_level

    def levels(self):
        """Return number of levels"""
        return len(self._levels)

    def check(self, _assumptions):
        assumptions = list()
        print("SELF.LEVELS", self._levels)
        if self.get_active_level() is not None:
            for i in range(0, self.get_active_level()):
                assumptions.append(self._levels[i])

        #activate solver
        #FIXME
        solver_var  = z3.Bool("vsolver#0")
        assumptions.append(solver_var)
        assumptions.extend(_assumptions)
        print("ASSUMPTIONs:\n", assumptions)
        res =  self._zsolver.check(*assumptions)

        print("CHECKING:\n", self._zsolver)
        return res

    def unsat_core(self):
        core = self._zsolver.unsat_core()
        #return [v for v in core if v is not a level atom]
        return core

    def model(self):
        return self._zsolver.model()

    def get_solver(self):
        return self._zsolver

    def push(self):
        assert(False)
        pass
    def pop(self):
        assert(False)
        pass


class InductiveGeneralizer(object):
    def __init__(self, solver, post_to_pre):
        self._solver = solver
        self._core = None
        self._post_to_pre = post_to_pre
        
    def free_arith_vars(self, fml):
        '''Returns the set of all integer uninterpreted constants in a formula'''
        seen = set([])
        vars = set([])

        def fv(seen, vars, f):
            # print("F\t:", f)
            # print("SEEN\t:", seen)
            if f in seen:
                return
            seen |= { f }
            # print("FREE_ARITH_CHECK:\n\t". f, f.sort(), f.decl().kind())
            if f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                vars |= { f }
            for ch in f.children():
                fv(seen, vars, ch)
                fv(seen, vars, fml)
        fv(seen, vars, fml)
        return vars


    def _mk_pre(self, post_lit):
        # XXX Implement renaming
        # print("_MK_PRE", post_lit)
        post_vs = self.free_arith_vars(post_lit)
        # print("_MK_PRE post_vs", post_vs)
        # print(self._post_to_pre)
        submap = [(post_v, self._post_to_pre[post_v]) for post_v in post_vs]
        print("_MK_PRE submap:", submap)
        pre_lit = z3.substitute(post_lit, submap)
        
        return pre_lit

    def _is_inductive(self, cube):
        print("checking inductive for cube:", cube)
        pre_lemma = [z3.Not(self._mk_pre(v)) for v in cube]

        pre_lemma_lit = self._solver.add_proxy(z3.Or(*pre_lemma))

        cube_lits = [self._solver.add_proxy(lit) for lit in cube]
        # self._solver._proxies_db.dump()
        print("CUBE_LITS:")
        for proxy_lit in cube_lits:
            print(proxy_lit, ":", self._solver.get_proxy(proxy_lit))
        print("PRE_LEMMA_LIT:")
        print(pre_lemma_lit, ":", self._solver.get_proxy(pre_lemma_lit))


        res = self._solver.check([pre_lemma_lit] + cube_lits)

        if res == z3.unsat:
            self._core = self._solver.unsat_core()

        return res


    def generalize(self, cube, lvl):
        """Inductive generalization of a cube given as a list"""
        saved_level = self._solver.get_active_level()
        self._solver.activate_level(lvl)


        for i in range(0, len(cube)):
            saved_lit = cube[i]
            cube[i] = z3.BoolVal(True)
            res = self._is_inductive([v for v in cube if not z3.is_true(v)])

            if res == z3.unsat:
                # generalized
                # only keep literals in the cube if they are also in the unsat core
                # literals that are not in the unsat core are not needed for unsat
                print("DROP SUCCESSFUL. New cube is:")
                print([v for v in cube if not z3.is_true(v)])
            else:
                # generalization failed, restore the literal
                cube[i] = saved_lit
                print("DROP FAILED")
                print("MODEL:", self._solver.model())
        # restore solver level for additional queries
        self._solver.activate_level(saved_level)

        # compute generalized cube
        return [v for v in cube if not z3.is_true(v)]


def main():
    filename = "Test3/pool_solver_vsolver#0_14.smt2"
    cube_filename = "Test3/test_cube"
    zsolver = z3.Solver()
    edb = ExprDb(filename)
    cube = edb.parse_cube(filename = cube_filename)
    print("PARSED CUBE", cube)
    # print("POST2PRE:", edb.post2pre())
    proxied_db = edb.proxies_db()
    s = SpacerSolver(zsolver, proxied_db)
    for e in edb.get_others():
        s.add(e)
    levels = edb.get_levels()
    for level_lit in levels:
        lvl, e_lvl = levels[level_lit]
        s.add_leveled(lvl, e_lvl)
    indgen = InductiveGeneralizer(s, edb.post2pre())
    indgen.generalize(cube, 2)

    del edb
main()
