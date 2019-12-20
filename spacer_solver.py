from ExprDb import ExprDb
import z3
import logging

log = logging.getLogger(__name__)
logging.basicConfig(level=logging.INFO)
class SpacerSolverProxyDb(object):
    def __init__(self, proxies_db):
        #map from proxy_lit to expr. Note that there maybe duplicated exprs
        self._proxies_db = proxies_db
    def size(self):
        return len(self._proxies_db)

    def find_lit(self, proxy_lit):
        '''
        return the constraint implied by the proxy literal
        '''
        return self._proxies_db[proxy_lit]

    def find_expr(self, e):
        '''
        return the first proxy that implies the constraint
        '''
        for (p,expr) in self._proxies_db.items():
            if e== expr:
                return p
        return None

    def add(self, e):
        # log.info("CURRENT SIZE", self.size())
        """Adds proxy and returns its literal"""
        new_lit = self.find_expr(e)
        if new_lit is not None:
            return new_lit
        else:
            new_lit = z3.Bool("spacer_proxy!#{}".format(self.size()))
            self._proxies_db[new_lit] = e
            return new_lit

    def dump(self):
        log.info("SIZE: %d", self.size())
        for (k,v) in self._proxies_db.items():
            log.info("%s <- %s", str(k), str(v))

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
        # log.info("ADDING:\n", e, "<-", proxy_lit)
        return proxy_lit

    def get_proxy(self, lit):
        return self._proxies_db.find_lit(lit)

    def find_expr(self, e):
        return self._proxies_db.find_expr(e)
    def add_leveled(self, lvl, e):
        """Add an assertion at a specified level"""
        self.ensure_level(lvl)
        level_lit = self._mk_level_lit(lvl)
        self._zsolver.add(z3.Implies(level_lit, e))

    def ensure_level(self, lvl):
        log.info("LEN SELF._LEVELS %d", len(self._levels))
        """Ensure that solver has lvl number of levels"""
        while (len(self._levels) <= lvl):
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
        log.info("SELF.LEVELS %s", self._levels)
        log.info(self.get_active_level())
        if self.get_active_level() is not None:
            for i in range(0, self.get_active_level()):
                log.info("DISABLE level %d", i)
                assumptions.append(z3.mk_not(self._levels[i]))
            for j in range(i+1, len(self._levels)):
                log.info("ACTIVATE level %d", j)
                assumptions.append(self._levels[j])

        #activate solver
        #FIXME
        solver_var  = z3.Bool("vsolver#1")
        ext_0_n_var = z3.Not(z3.Bool("INV_ext0_n"))
        assumptions.append(solver_var)
        assumptions.append(ext_0_n_var)
        assumptions.extend(_assumptions)
        log.info("ASSUMPTIONs:\n%s", str(assumptions))
        res =  self._zsolver.check(*assumptions)

        # log.info("CHECKING:\n", self._zsolver)
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
    def __init__(self, solver, post_to_pre, use_unsat_core = True):
        self._solver = solver
        self._core = None
        self._post_to_pre = post_to_pre
        self._use_unsat_core = use_unsat_core
    def free_arith_vars(self, fml):
        '''Returns the set of all integer uninterpreted constants in a formula'''
        seen = set([])
        vars = set([])

        def fv(seen, vars, f):
            # log.info("F\t:\n", f)
            # log.info("SEEN\t:\n", seen)
            if f in seen:
                return
            seen |= { f }
            # log.info("FREE_ARITH_CHECK:\n\t". f, f.sort(), f.decl().kind())
            if f.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                vars |= { f }
            for ch in f.children():
                fv(seen, vars, ch)
                fv(seen, vars, fml)
        fv(seen, vars, fml)
        return vars


    def _mk_pre(self, post_lit):
        # XXX Implement renaming
        # log.info("_MK_PRE", post_lit)
        post_vs = self.free_arith_vars(post_lit)
        # log.info("_MK_PRE post_vs", post_vs)
        # log.info(self._post_to_pre)
        submap = [(post_v, self._post_to_pre[post_v]) for post_v in post_vs]
        # log.info("_MK_PRE submap:\n", submap)
        pre_lit = z3.substitute(post_lit, submap)
        
        return pre_lit

    def check_inductive(self, cube, level):
        saved_level = self._solver.get_active_level()
        self._solver.activate_level(level)

        log.info("checking inductive for cube:\n%s at level %s", cube, level)
        pre_lemma = [z3.mk_not(self._mk_pre(v)) for v in cube]

        pre_lemma_lit = self._solver.add_proxy(z3.Or(*pre_lemma))

        cube_lits = [self._solver.add_proxy(lit) for lit in cube]
        # self._solver._proxies_db.dump()
        log.info("CUBE_LITS:\n")
        for proxy_lit in cube_lits:
            log.info("%s : %s", proxy_lit, self._solver.get_proxy(proxy_lit))
        log.info("PRE_LEMMA_LIT:\n %s : %s", pre_lemma_lit, self._solver.get_proxy(pre_lemma_lit))


        res = self._solver.check([pre_lemma_lit] + cube_lits)

        if res == z3.unsat:
            self._core = self._solver.unsat_core()

        # restore solver level for additional queries
        self._solver.activate_level(saved_level)

        return res


    def generalize(self, cube, lvl):
        """Inductive generalization of a cube given as a list"""

        for i in range(0, len(cube)):
            saved_lit = cube[i]
            cube[i] = z3.BoolVal(True)
            res = self.check_inductive([v for v in cube if not z3.is_true(v)], lvl)
            
            if res == z3.unsat:
                # generalized
                # only keep literals in the cube if they are also in the unsat core
                # literals that are not in the unsat core are not needed for unsat
                log.info("DROP SUCCESSFUL. New cube is:\n")
                log.info([v for v in cube if not z3.is_true(v)])
                log.debug("UNSAT CORE:\n %s", self._solver.unsat_core())
                # use the unsat core
                for j in range(0, len(cube)):
                    if cube[j]==z3.BoolVal(True): continue
                    p = self._solver.find_expr(cube[j])
                    if p not in self._solver.unsat_core():
                        log.debug(cube[j], "<-", p, " is not in the UNSAT CORE. Drop")
                        cube[j] = z3.BoolVal(True)
            else:
                # generalization failed, restore the literal
                cube[i] = saved_lit
                log.info("DROP FAILED")
                log.debug("WAS CHECKING:\n %s", self._solver.get_solver().sexpr())
                log.debug("MODEL: %s", self._solver.model())
                # compute generalized cube

        return [v for v in cube if not z3.is_true(v)]


def main():
    filename = "Test7_unroll4/pool_solver_vsolver#1_37.smt2"
    cube_filename = "Test7_unroll4/test_cube37"
    zsolver = z3.Solver()
    edb = ExprDb(filename)
    cube = edb.parse_cube(filename = cube_filename)
    log.info("PARSED CUBE:\n %s", cube)
    # log.info("POST2PRE: %s", edb.post2pre())
    proxied_db = edb.proxies_db()
    s = SpacerSolver(zsolver, proxied_db)
    for e in edb.get_others():
        s.add(e)
    levels = edb.get_levels()
    for level_lit in levels:
        log.info("ADDING LEMMAS AT LEVEL %s", level_lit)
        for (lvl, e_lvl) in levels[level_lit]:
            log.info("\t %s %s", lvl, e_lvl)
            s.add_leveled(lvl, e_lvl)
    indgen = InductiveGeneralizer(s, edb.post2pre())
    inducted_cube = indgen.generalize(cube, 1)
    #validate
    print("FINAL CUBE:\n", inducted_cube)
    res = indgen.check_inductive(inducted_cube, 1)
    print(res)
    assert(res==z3.unsat)
    del edb
main()
