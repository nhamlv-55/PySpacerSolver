
class SpacerSolverProxyDb(object):
    def __init__(self):
        pass

    def size(self):
        pass

    def find(self, e):
        pass

    def add(self, e):
        """Adds proxy and returns its literal"""
        pass

    def push(self):
        pass
    def pop(self):
        pass

class SpacerSolver(object):
    def __init__(self, zsolver):
        self._zsolver = zsolver
        self._levels = []
        self._proxies_db = SpacerSolverProxyDb() 
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

    def check(self, *_assumptions):
        assumptions = list()

        if self.get_active_level() is not None:
            for i in range(0, self.get_active_level()):
                assumptions.append(self._levels[i])

        assumptions.extend(_assumptions)
        return self._zsolver.check(*assumptions)

    def unsat_core(self):
        core = self._zsolver.unsat_core()
        #return [v for v in core if v is not a level atom]
        return core


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


    def _mk_pre(self, lit):
        # XXX Implement renaming
        return None

    def _is_inductive(self, cube):
        pre_lemma = [z3.Not(self._mk_pre(v)) for v in cube]
        pre_lemma_lit = self._solver.add_proxy(z3.Or(*pre_lemma))

        cube_lits = [self._solver.add_proxy(lit) for lit in cube]

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
            res = self._is_inductive(self, [v for v in cube if not z3.is_true(v)])

            if res == z3.unsat:
                # generalized
                # only keep literals in the cube if they are also in the unsat core
                # literals that are not in the unsat core are not needed for unsat
                continue
            else:
                # generalization failed, restore the literal
                cube[i] = saved_lit
            pass

        # restore solver level for additional queries
        self._solver.activate_level(saved_level)

        # compute generalized cube
        return [v for v in cube if not z3.is_true(v)]


