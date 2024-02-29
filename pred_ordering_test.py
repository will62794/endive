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


# print(e1.to_ast())
# print(e2.to_ast())
# print(e1.equivalent(e2))

# preds = ["A", "B", "C"]

NUM_PREDS = 2
preds = [f"p{ind}" for ind in range(NUM_PREDS)]

num_invs = 2500
num_conjuncts = 2
# res = mc.generate_invs(preds, num_invs, min_num_conjuncts=num_conjuncts, max_num_conjuncts=num_conjuncts)

uniq_ps = []
for i in range(5000):
    p = mc.pyeda_rand_pred(preds, num_terms=3)
    exists_equiv = False
    for a in uniq_ps:
        if p.equivalent(a):
            exists_equiv = True
            break
    if not exists_equiv:
        uniq_ps.append(p)
    # print(p)
    # print("===")
print(f"Generated {len(uniq_ps)} unique ps.")
for p in uniq_ps:
    print(p)

# print(res)
# invs = res["pred_invs"]
invs = uniq_ps

epred = mc.PredExpr(invs[0])
print("EPRED:", epred)


print("All generated invariants:")
for inv in invs:
    print(inv)
    pass
print(f"Generated {len(invs)} total unique invariant candidates.")
print(f"We expected 2^(2^{len(preds)}) = {2**(2**len(preds))} unique invariants for {len(preds)} predicates ({preds}).")

num_implication_orderings = 0
edges = []
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
            edges.append((symb_inv, symb_inv2))
        if impliesback.equivalent(True) and not impliesforward.equivalent(True):
            # print(f"comparing {symb_inv} <= {symb_inv2}")
            # print("  implies:", impliesback)
            num_implication_orderings += 1
            edges.append((symb_inv2, symb_inv))

            # print("  implies:", impliesback)
print("TOTAL IMPLICATION ORDERINGS:", num_implication_orderings)
for e in edges:
    print(f'"{e[0]}"', "->", f'"{e[1]}"')
# print(edges)