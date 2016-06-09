from predicate import Predicate
from grounder import Operator
from myerror import MyError
from formula import Formula, And, Primitive, Forall, When, Xor, Not, Oneof, Or
import random


class Literal(Formula):
    def __init__(self, name, f, jt):
        super(Literal, self).__init__('Literal', [])

        self.f = f
        self.type = name
        if self.type == 'action':
            assert isinstance(f, Operator)
            self.params = tuple([param[0] for param in self.f.parameters])
            self.fname = f.name
            self.j = jt[0]
            self.t = jt[1]
        elif self.type == 'fluent':
            assert isinstance(f, Predicate)
            self.fname = f.name
            self.j = jt[0]
            self.t = jt[1]
            if f.args is not None:
                if len(f.args)!=0:
                    self.params = tuple([arg[0] for arg in f.args])
                else:
                    self.params = ()
            else:
                if len(f.ground_args) != 0:
                    self.params = tuple([arg[0] for arg in f.ground_args])
                else:
                    self.params = ()
        else:
            assert isinstance(f, tuple)
            self.j = None
            self.t = jt
            self.fname = 'djk'
            self.params = f
        self.args = (self.fname, self.params, jt)

    def __str__(self):
        return self.type + ' ' + ', '.join([str(a) for a in self.args])

    def __eq__(self, other):
        return (self.__class__ == other.__class__) and (self.type == other.type) and (self.args == other.args)

    def __hash__(self):
        return hash((self.type + ', '.join([str(a) for a in self.args])))
#     def literal(self, jkt):
#         if self.type == 'action':
#             assert (len(jkt) == 2)
#         elif self.type == 'fluent':
#             assert (len(jkt) == 2)
#         else:
#             assert (len(jkt) == 1)
#
#         return(Literal(self, jkt))
#
# class Literal(Formula):
#     def __init__(self, atom_obj, jkt):
#         super(Literal, self).__init__('Literal', [])
#         self.atom = atom_obj
#         self.name = 'Literal'
#         self.jkt = jkt
#         if len(jkt) == 2:
#             self.j = jkt[0]
#             self.t = jkt[1]
#         elif len(jkt) == 1:
#             self.t = jkt[0]
#     def __str__(self):
#         return 'literal ('+str(self.atom)+', ' +', '.join(['%d' % j for j in self.jkt])+')'
#     def __eq__(self,f):
#         return self.atom == f.atom and self.jkt == f.jkt
#     def __hash__(self):
#         return hash((self.atom.__hash__, self.jkt))

class Logic:
    def __init__(self):
        self.name = []

    def lit(self, f, j, t):

        if f is None:
            return None
        if f.__class__ == Predicate:
            return Literal('fluent',f, (j,t))
        if f.name == 'Primitive':
            return Literal('fluent',f.predicate, (j,t))
        elif f.name == 'when':
            a = f.condition
            b = f.result
            a_lit = self.lit(a,j,t-1)
            b_lit = self.lit(b, j, t)
            newf = When([a_lit, b_lit])
            return self.norm(newf)
        else:
            newargs = [self.lit(a,j,t) for a in f.args]
            newf = f.__class__(newargs)
            return self.norm(newf)

    def if_then(self, condition, result):
        iff = Not([condition])
        thenf = result
        return Or([Not([iff]), thenf])

    def norm(self, formula):
        name = formula.name
        if (name == 'Literal') | (name == 'Primitive'):
            return formula

        elif name == 'not':
            if len(formula.args) != 1:
                raise MyError('not with more args')
            if (formula.args[0].name == 'Literal') | (formula.args[0].name == 'Primitive'):
                return formula
            elif formula.args[0].name == 'and':
                new_formula = Or([Not([a]) for a in formula.args[0].args])
                return self.norm(new_formula)
            elif formula.args[0].name == 'or':
                new_formula = And([Not([a]) for a in formula.args[0].args])
                return self.norm(new_formula)
            elif formula.args[0].name == 'not':
                new_formula = formula.args[0].args[0]
                return self.norm(new_formula)
            else:
                raise MyError('Formula in NOT:{}'.format(formula.args[0].name))
        elif name == 'and':
            for f in formula.args:
                if (f.name == 'Literal') or (f.name == 'Primitive'):
                    pass
                elif f.name == 'and':
                    rest = formula.args[:]
                    rest.remove(f)
                    rest.extend(f.args)
                    new_formula = And(rest)
                    return self.norm(new_formula)
                elif f.name == 'when':
                    f1 = self.norm(f)
                    rest = formula.args[:]
                    rest.remove(f)
                    rest.append(f1)
                    new_formula = And(rest)
                    return self.norm(new_formula)
                elif f.name == 'or' or f.name == 'not':
                    f1 = self.norm(f)
                    if f1 != f:
                        rest = formula.args[:]
                        rest.remove(f)
                        rest.append(f1)
                        new_formula = And(rest)
                        return self.norm(new_formula)
                else:
                    raise MyError('j')
            return formula

        elif name == 'or':
            if len(formula.args) == 1:
                return self.norm(formula.args[0])
            for arg in formula.args:
                if arg.name == 'and':
                    rest = formula.args[:]
                    rest.remove(arg)
                    new_list = []
                    for f in arg.args:
                        new_new_list = rest[:]
                        new_new_list.append(f)
                        new_list.append(Or(new_new_list))
                    new_formula = And(new_list)
                    return self.norm(new_formula)
                elif arg.name == 'or':
                    rest = formula.args[:]
                    rest.remove(arg)
                    new_list = arg.args[:]
                    new_list.extend(rest)
                    new_formula = Or(new_list)
                    return self.norm(new_formula)
                elif arg.name == 'not':
                    arg2 = self.norm(arg)
                    if arg2 != arg:
                        rest = formula.args[:]
                        rest.remove(arg)
                        rest.append(arg2)
                        new_formula = Or(rest)
                        return self.norm(new_formula)
                elif arg.name == 'when':
                    rest = formula.args[:]
                    rest.remove(arg)
                    arg2 = self.norm(arg)
                    return self.norm(Or(rest+[arg2]))

            return formula
        elif name == 'when':
            # when(a,b) <=> or(not-a, b)
            a = formula.condition
            b = formula.result
            new_a = Not([a])
            new_formula = Or([new_a, b])
            return self.norm(new_formula)
        else:
            raise MyError('not enough')

    def norm_init(self, formula):
        oneofs = []
        ooset = set([])
        new_args = formula.args[:]
        for f in formula.args:
            if f.name == 'oneof':
                oneofs.append(f)
                new_args.remove(f)
        oneargs = [[]]
        for o in oneofs:
            newnew = []
            for oo in o.args:
                nots = o.args[:]
                nots.remove(oo)
                newnew.extend([[oo] + [Not([n]) for n in nots] + a for a in oneargs])
            oneargs = newnew
        return oneargs, self.norm(And(new_args))

'''
poss = ['p{0}'.format(i) for i in range(10)]
preds = []
for i in range(5):
    preds.extend([Predicate('pos', [(pos, str(i))]) for pos in poss])
atoms = set([Atom('fluent', pred) for pred in preds])

# l = [a.literal([]) for a in atoms]
# f = l[5]
# for j in range(4):
#     v = l[j]
#     vm = l[9-j]
#     k = random.randint(0,3)
#     rels = ['not', 'or', 'and', 'when']
#     if k == 0:
#         f = Not([And([f,v])])
#     elif k == 1:
#         f = Or([f, v, vm])
#     elif k == 2:
#         f = And([f, v, vm])
#     elif k == 3:
#         f = When(f,v)
# L = Logic()
# fn = L.norm(f)


# op= Operator('move', [('p1', 'pos')],None,None,None)
# pr = Predicate('p',[])
# a = Atom('fluent', pr)
# l = a.literal([0,0])
# o = Or([l, l])
# print o
'''