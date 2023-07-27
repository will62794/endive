import z3
from z3 import solve,ForAll

# A = z3.DeclareSort('A')

RM, (n1, n2, n3) = z3.EnumSort('RM', ('n1', 'n2', 'n3'))
RmState, (init, prepared, aborted) = z3.EnumSort('RmState', ('init', 'prepared', 'aborted'))
TmState, (tminit, tmprepared, tmaborted) = z3.EnumSort('TmState', ('init', 'prepared', 'aborted'))

x,y = z3.Consts("x y", RM)

rmState = z3.Function('rmState_sv', RM, RmState)
tmState = z3.Function('tmState_sv', TmState)

Init = z3.And([
    ForAll([x], rmState(x) == init),
    ForAll([x], tmState() == tminit)
])
solve(Init)

# rmState
# tmState
# tmPrepared
# msgs


# a, b = Ints('a b')
# x, y = Reals('x y')
# solve(0 < x, 0 < y, x + y < 1, x <= y)