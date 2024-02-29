import mc
import pyeda
import pyeda.inter
import logging
import sys

log_format = '%(message)s'
log_level = logging.DEBUG
logging.basicConfig(stream=sys.stdout, format=log_format, filemode='w', level=log_level)


# (x_000) | (~(x_001) | ~((x_001)))
# (x_001) | ~(~(x_001) | ~(~(x_000)))
e1 = pyeda.inter.expr("(x_000) | (~(x_002) | ~((x_001)))")
e2 = pyeda.inter.expr("(x_000) | (~(x_001) | ~((x_002)))")

for i in range(20):
    p = mc.pyeda_rand_pred(["A","B"], max_terms=3)
    print(p)

# print(e1.to_ast())
# print(e2.to_ast())
# print(e1.equivalent(e2))

exit(0)

# preds = ["A", "B", "C"]

NUM_PREDS = 3
preds = [f"p{ind}" for ind in range(NUM_PREDS)]

num_invs = 2500
num_conjuncts = 2
res = mc.generate_invs(preds, num_invs, min_num_conjuncts=num_conjuncts, max_num_conjuncts=num_conjuncts)
# print(res)
invs = res["pred_invs"]
print("All generated invariants:")
for inv in invs:
    print(inv)
    pass
print(f"Generated {len(invs)} total unique invariant candidates.")
print(f"We expected 2^(2^{len(preds)}) = {2**(2**len(preds))} unique invariants for {len(preds)} predicates ({preds}).")

num_implication_orderings = 0
for invi,inv in enumerate(invs):
    # symb_inv = invs_symb[invi]
    symb_inv = pyeda.inter.expr(inv)
    # print(symb_inv.to_ast())

    for invi2,inv2 in enumerate(invs):
        symb_inv2 = pyeda.inter.expr(inv2)
        impliesforward = pyeda.inter.Implies(symb_inv, symb_inv2, simplify=True)
        impliesback = pyeda.inter.Implies(symb_inv2, symb_inv, simplify=True)
        
        # comparing Or(~x_017, ~x_000, x_013) and Or(x_007, x_016, ~x_011)

        if impliesforward.equivalent(True) and not impliesback.equivalent(True):
            # print(f"comparing {symb_inv} => {symb_inv2}")
            # print("  implies:", impliesforward)
            num_implication_orderings += 1
        if impliesback.equivalent(True) and not impliesforward.equivalent(True):
            # print(f"comparing {symb_inv} <= {symb_inv2}")
            # print("  implies:", impliesback)
            num_implication_orderings += 1
            # print("  implies:", impliesback)
print("TOTAL IMPLICATION ORDERINGS:", num_implication_orderings)