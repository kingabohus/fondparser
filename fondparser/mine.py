from predicate import Predicate
import os
from formula import Formula, And, Primitive, Forall, When, Xor, Not, Oneof, Or
from grounder import GroundProblem, Operator
from helper_classes import Literal, Logic
from myerror import MyError


class T2CNF:
    def __init__(self, p, h):
        self.problem = p
        self.initial = p.init
        # self.actions = p.actions
        self.goal = p.goal
        # self.type_to_obj = p.type_to_obj
        # self.objects = p.obj_to_type
        self.fluents = p.fluents
        self.operators = p.operators
        self.precs = {}
        self.effects = {}
        self.observes = {}
        self.adds_fluent = {}#use
        self.dels_fluent = {}#use
        self.horizon = h
        self.j = 1
        self.logic = Logic()
        self.jk = []
        self.fluent_lits = []
        self.op_lits = []
        self.djk_lits = []
        self.all_literals = []
        self.initial_lits = None
        self.subproblems = []
        self.init_known = None
        self.lit_dict = {}
        self.lit_lookup = {}
        self.dg_atom = Predicate('DG', None, [])
        self.fluents.add(self.dg_atom)
        self.end_atom = Operator('End', [], self.goal, None, And([Primitive(self.dg_atom)]))
        self.operators.add(self.end_atom)
        # self.wait_atom = Operator('Wait', [], And([Primitive(self.dg_atom)]), None, And([Primitive(self.dg_atom)]))
        # self.operators.add(self.wait_atom)

    def get_subproblems(self):
        initial = self.initial
        self.subproblems, self.init_known = self.logic.norm_init(initial)
        self.j = len(self.subproblems)
        for j in range(self.j-1):
            for k in range(j+1, self.j):
                self.jk.append((j,k))

    # def clean_fluent(self,fluent):
    #     if fluent.args is not None:
    #         fluent.ground_args = fluent.args
    #         fluent.args = None

    def mentioned_by_formula(self, formula):
        mentioned = set([])
        if formula.name != 'and':
            raise MyError('has to start with and')
        for arg in formula.args:
            if arg.name == 'Primitive':
                mentioned.add(arg.predicate)
            elif arg.name == 'not':
                mentioned.add(arg.args[0].predicate)
            elif arg.name == 'or':
                for f in arg.args:
                    if f.name == 'Primitive':
                        mentioned.add(f.predicate)
                    elif f.name == 'not':
                        mentioned.add(f.args[0].predicate)
            elif arg.name == 'when':
                for c in arg.condition.args:
                    if c.name == 'Primitive':
                        mentioned.add(c.predicate)
                    elif c.name == 'not':
                        mentioned.add(c.args[0].predicate)
                for r in arg.result.args:
                    if r.name == 'Primitive':
                        mentioned.add(r.predicate)
                    elif r.name == 'not':
                        mentioned.add(r.args[0].predicate)
            else:
                raise MyError('turn it up')
        return mentioned

    def obsoletes(self):
        initmen = self.mentioned_by_formula(self.init_known)
        initoneof = set([])
        for i in self.subproblems[0]:
            if i.name == 'Primitive':
                initoneof.add(i.predicate)
            elif i.name == 'not':
                initoneof.add(i.args[0].predicate)
        self.initnot = (self.fluents - initmen - initoneof)
        allomen = set([])
        for o in self.operators:
            if o.effect is not None:
                omen = self.mentioned_by_formula(o.effect)
                allomen = allomen | omen

        self.never_add = self.fluents - initmen - allomen

        self.impossible_ops = set([])
        for o in self.operators:
            if o.precondition is not None:
                for f in o.precondition.args:
                    if (f.name == 'Primitive') and (f.predicate in self.never_add):
                        self.impossible_ops.add(o)

        self.possible_ops = self.operators - self.impossible_ops

    def lit_formula(self, f,j,t):
        if f is None:
            return None
        if f.__class__ == Predicate:
            return self.lit_lookup[f, j, t]
        if f.name == 'Primitive':
            return self.lit_lookup[f.predicate, j, t]
        elif f.name == 'when':
            a = f.condition
            b = f.result
            a_lit = self.lit_formula(a, j, t - 1)
            b_lit = self.lit_formula(b, j, t)
            newf = When(a_lit, b_lit)
            return newf
        else:
            newargs = [self.lit_formula(a, j, t) for a in f.args]
            newf = f.__class__(newargs)
            return newf

    def create_literals(self):

        self.all_atoms = list(self.fluents) + list(self.possible_ops) + self.jk
        for t in range(self.horizon):
            for j in range(self.j):
                for f in self.fluents:
                    lit = Literal('fluent', f, (j,t))
                    self.fluent_lits.append(lit)
                    self.lit_lookup[f, j, t] = lit
        for t in range(self.horizon-1):
            for j in range(self.j):
                for o in self.possible_ops:
                    lit = Literal('action', o, (j,t))
                    self.op_lits.append(lit)
                    self.lit_lookup[o, j, t] = lit
                    self.precs[lit] = self.lit_formula(o.precondition, j,t)
                    self.effects[lit] = self.lit_formula(o.effect, j, t+1)
                    self.observes[lit] = self.lit_formula(o.observe,j,t+1)
                    if o.name == 'End':
                        self.effects[lit] = And([ self.effects[lit], self.lit_formula(Primitive(self.dg_atom), j, self.horizon-1)])

        for t in range(self.horizon):
            for djk in self.jk:
                lit = Literal('D', djk, t)
                self.djk_lits.append(Literal('D', djk, t))
                self.lit_lookup['D',djk, t] = lit

        self.all_literals = self.fluent_lits + self.op_lits + self.djk_lits
        self.goal_lits = [self.lit_lookup[self.dg_atom, j, self.horizon-1] for j in range(self.j)]
        self.initial_lits = [self.lit_formula(self.init_known, j, 0) for j in range(self.j)]
        self.subinit_lits = [self.lit_formula(And(self.subproblems[j]),j, 0) for j in range(self.j)]
        self.initnot_lits = [self.lit_formula(And([Not([Primitive(i)])   for i in self.initnot]),j,0) for j in range(self.j)]

        d = 1
        for l in self.all_literals:
            self.lit_dict[l] = d
            d += 1

    def adds_dels(self):
        for f in self.fluent_lits:
            self.adds_fluent[f] = []
            self.dels_fluent[f] = []

        for a in self.effects:
            effect = self.effects[a]
            if effect is None:
                pass
            elif effect.name != 'and':
                raise MyError('effect isnt and')
            else:
                for arg in effect.args:
                    if arg.name == 'Primitive':
                        raise MyError('this should not be here')
                    elif arg.name == 'Literal':
                        self.adds_fluent[arg].append(And([a]))
                    elif arg.name == 'not':
                        if arg.args[0].name != 'Literal':
                            raise MyError('nope')
                        else:
                            self.dels_fluent[arg.args[0]].append(And([a]))
                    elif arg.name == 'when':
                        result = arg.result
                        if result.name != 'and':
                            raise MyError('when result ?')
                        for r in result.args:
                            if r.name == 'Literal':
                                self.adds_fluent[r].append(And([a, arg.condition]))
                            elif r.name == 'not':
                                self.dels_fluent[r.args[0]].append(And([a, arg.condition]))
                            else:
                                raise MyError('whenresult {}'.format(r.name))
                    else:
                        raise MyError('whhaaaaa')

    def translate(self):
        self.file = open('try.txt' ,'w')
        self.check = open('check.txt', 'w')
        self.add_initial()
        self.add_actions()
        self.add_observes()
        self.add_persistence()
        self.add_restrictions()
        self.add_goals()
        self.file.close()
        self.check.close()
        num_clauses = sum(1 for line in open('try.txt'))
        num_vars = len(self.all_literals)
        cnf_file = open('try.cnf', 'w')
        cnf_file.write('p cnf {0} {1}\n'.format(num_vars,num_clauses))
        for line in open('try.txt'):
            cnf_file.write(line)
        cnf_file.close()

    def add_initial(self):
        self.check.write('INITIALS \n')
        for i in self.initial_lits:
            self.printtofile(i)
        for si in self.subinit_lits:
            self.printtofile(si)
        for ni in self.initnot_lits:
            self.printtofile(ni)
        for dg in [self.lit_lookup[self.dg_atom, j, 0] for j in range(self.j)]:
            self.printtofile(Not([dg]))

    def add_actions(self):
        self.check.write('ACTIONS \n')
        for o in self.op_lits:
            if self.precs[o] is not None:
                self.printtofile(When(o, self.precs[o]))
            if self.effects[o] is not None:
                self.printtofile(When(o, self.effects[o]))

    def add_observes(self):
        self.check.write('OBSERVES \n')
        for djk in self.jk:
            self.printtofile(Not([Literal('D', djk, 0)]))

        for (j,k) in self.jk:
            for t in range(self.horizon-1):
                djkt = self.lit_lookup['D', (j,k), t+1]
                djkt0 = self.lit_lookup['D', (j,k), t]
                self.printtofile(When(djkt0, djkt))
                for o in self.possible_ops:
                    if o.observe is None:
                        ajt = self.lit_lookup[o,j,t]
                        akt = self.lit_lookup[o,k,t]
                        (When(And([Not([djkt0]), ajt]), Not([djkt])))
                        (When(And([Not([djkt0]), akt]), Not([djkt])))
                    else:
                        obs = o.observe
                        ajt = self.lit_lookup[o, j, t]
                        akt = self.lit_lookup[o, k, t]
                        obsjt = self.lit_lookup[obs, j, t]
                        obskt = self.lit_lookup[obs, k, t]
                        iff = And([Not([djkt0]), ajt, obsjt, Not([obskt]) ])
                        thenf = djkt
                        self.printtofile(When(iff,thenf))
                        iff = And([Not([djkt0]), ajt, obskt, Not([obsjt]) ])
                        self.printtofile(When(iff,thenf))

                        iff = And([Not([djkt0]), akt, obsjt, Not([obskt])])
                        thenf = djkt
                        self.printtofile(When(iff, thenf))
                        iff = And([Not([djkt0]), akt, obskt, Not([obsjt])])
                        self.printtofile(When(iff, thenf))

                        iff = And([Not([djkt0]), ajt, obsjt, obskt])
                        thenf = Not([djkt])
                        self.printtofile(When(iff, thenf))
                        iff = And([Not([djkt0]), ajt, Not([obskt]), Not([obsjt])])
                        self.printtofile(When(iff, thenf))

                        iff = And([Not([djkt0]), akt, obsjt, obskt])
                        thenf = Not([djkt])
                        self.printtofile(When(iff, thenf))
                        iff = And([Not([djkt0]), akt, Not([obskt]), Not([obsjt])])
                        self.printtofile(When(iff, thenf))

    def add_goals(self):
        self.check.write('GOALS \n')
        for dg in self.goal_lits:
            self.printtofile(dg)

    def add_persistence(self):
        self.check.write('PERSISTENCE \n')
        for j in range(self.j):
            for t in range(self.horizon-1):
                for p in self.fluents:
                    pjt = self.lit_lookup[p,j,t+1]
                    pjt0 = self.lit_lookup[p,j,t]
                    adds = self.adds_fluent[pjt]

                    if len(adds) > 0:
                        iff = And([Not([pjt0])] + [Not([a]) for a in adds])
                        thenf = Not([pjt])
                        self.printtofile(When(iff, thenf))
                    else:
                        self.printtofile(When(Not([pjt0]), Not([pjt])))

                    dels = self.dels_fluent[pjt]
                    if len(dels) > 0:
                        iff = And([pjt0] + [Not([a]) for a in dels])
                        thenf = pjt
                        self.printtofile(When(iff, thenf))
                    else:
                        self.printtofile(When(pjt0, pjt))

    def add_restrictions(self):
        self.check.write('RESTRICTIONS \n')
        pos = list(self.possible_ops)
        for i in range(len(pos)-1):
            for l in range(i+1, len(pos)):
                a1 = pos[i]
                a2 = pos[l]
                for t in range(self.horizon-1):
                    for j in range(self.j):
                        a1jt = self.lit_lookup[a1, j, t]
                        a2jt = self.lit_lookup[a2, j, t]
                        self.printtofile(When(a1jt, Not([a2jt])))
                    for (j,k) in self.jk:
                        a1jt = self.lit_lookup[a1, j, t]
                        a2kt = self.lit_lookup[a2, k, t]
                        a1kt = self.lit_lookup[a1, k, t]
                        a2jt = self.lit_lookup[a2, j, t]
                        djkt = self.lit_lookup['D', (j,k), t]
                        self.printtofile(When(And([a1jt, a2kt]), djkt))
                        self.printtofile(When(And([a1kt, a2jt]), djkt))
        for o in pos:
            for t in range(self.horizon-1):
                for (j, k) in self.jk:
                    ajt = self.lit_lookup[o,j,t]
                    akt = self.lit_lookup[o,k,t]
                    djkt = self.lit_lookup['D', (j,k), t]
                    self.printtofile(When(And([ajt, Not([djkt])]),akt ))
                    self.printtofile(When(And([akt, Not([djkt])]), ajt))

        for j in range(self.j):
            for t in range(self.horizon-1):
                # alist = [self.lit_lookup[o,j,t] for o in pos]
                # dgjt = self.lit_lookup[self.dg_atom, j,t]
                # self.printtofile(Or([dgjt]+alist))
                goallist = [self.lit_lookup[g.predicate,j,t] for g in self.goal.args ]
                enda = self.lit_lookup[self.end_atom, j, t]
                self.printtofile(When(And(goallist), enda))
                dgjt = self.lit_lookup[self.dg_atom, j,t]
                alist = [self.lit_lookup[o, j, t] for o in pos]
                self.printtofile(When(dgjt, Not([Or(alist)])))






    def printtofile(self, formula):
        dict = self.lit_dict
        formula = self.logic.norm(formula)

        if formula.name == 'and':
            for arg in formula.args:
                self.printtofile(arg)

        elif formula.name == 'Literal':
            self.check.write('{0} \n'.format(formula))
            num = dict[formula]
            self.file.write('{0} 0\n'.format(num))
        elif formula.name == 'not':
            if len(formula.args) != 1:
                raise MyError('problem')
            self.check.write('{0} \n'.format(formula))
            num = dict[formula.args[0]]
            self.file.write('-{0} 0\n'.format(num))

        elif formula.name == 'or':
            for arg in formula.args:
                if arg.name == 'Literal':
                    self.check.write('{0} or '.format(arg))
                    num = dict[arg]
                    self.file.write('{0} '.format(num))
                elif arg.name == 'not':
                    self.check.write('{0} or '.format(arg))
                    num = dict[arg.args[0]]
                    self.file.write('-{0} '.format(num))
                else:
                    raise MyError('or')
            self.check.write('\n')
            self.file.write('0\n')
        else:
            raise MyError('nop')


domain = './benchmarks/smallroom/domain.pddl'
problem = './benchmarks/smallroom/problem.pddl'


# domain = './benchmarks/wumpus/d.pddl'
# problem = './benchmarks/wumpus/p.pddl'

#
# domain = './benchmarks/localize/dsliding-doors-3.pddl'
# problem = './benchmarks/localize/psliding-doors-3.pddl'

#domain = './benchmarks/doors/ddoors-5.pddl'
#problem = './benchmarks/doors/pdoors-5.pddl'

# domain = './benchmarks/blocks/domain.pddl'
# problem = './benchmarks/blocks/p3.pddl'

# p = parse.Problem(domain, problem)
p = GroundProblem(domain, problem)
horizon = 10

CNF = T2CNF(p, horizon)

CNF.get_subproblems()
CNF.obsoletes()
CNF.create_literals()
CNF.adds_dels()
CNF.translate()

print 'ayyoo'
execfile('callsat.py')