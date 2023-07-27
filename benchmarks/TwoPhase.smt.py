import z3
from z3 import solve,ForAll,Exists

# A = z3.DeclareSort('A')

RM, (n1, n2, n3) = z3.EnumSort('RM', ('n1', 'n2', 'n3'))
RmState, (init, prepared, aborted) = z3.EnumSort('RmState', ('init', 'prepared', 'aborted'))
TmState, (tminit, tmprepared, tmaborted) = z3.EnumSort('TmState', ('init', 'prepared', 'aborted'))

x,y = z3.Consts("x y", RM)

rmState = z3.Function('rmState_sv', RM, RmState)
tmState = z3.Function('tmState_sv', TmState)
tmPrepared = z3.Function('tmPrepared_sv', RM, z3.BoolSort())
msgsCommit = z3.Function('msgsCommit_sv', z3.BoolSort())
msgsAbort = z3.Function('msgsAbort_sv', z3.BoolSort()) 
msgsPrepared = z3.Function('msgsAbort_sv', RM, z3.BoolSort())

rmState_next = z3.Function('rmState_sv_next', RM, RmState)
tmState_next = z3.Function('tmState_sv_next', TmState)
tmPrepared_next = z3.Function('tmPrepared_sv_next', RM, z3.BoolSort())
msgsCommit_next = z3.Function('msgsCommit_sv_next', z3.BoolSort())
msgsAbort_next = z3.Function('msgsAbort_sv_next', z3.BoolSort()) 
msgsPrepared_next = z3.Function('msgsAbort_sv_next', RM, z3.BoolSort())

Init = z3.And([
    ForAll([x], rmState(x) == init),
    ForAll([x], tmState() == tminit),
    ForAll([x], tmPrepared(x) == False),
    ForAll([x], msgsCommit() == False),
    ForAll([x], msgsAbort() == False),
    ForAll([x], msgsPrepared(x) == False)
])

rm = z3.Consts("rm", RM)

def TMRecvPrepared(sv,sv_next):
    return Exists([rm], z3.And([
            sv["tmState"](rm) == init,
            sv["msgsPrepared"](rm),
            sv_next["tmPrepared_next"](rm) == True,
            sv_next["tmState"] == sv["tmState"]
        ])
    )


s = z3. Solver()
s.add(Init)
s.check()
m = s.model()
print(m)

# print(type(m))
# v = m[rmState]
# print(m.evaluate(rmState(n2)))
# # (n1)
# print(v)


# rmState
# tmState
# tmPrepared
# msgs


# a, b = Ints('a b')
# x, y = Reals('x y')
# solve(0 < x, 0 < y, x + y < 1, x <= y)