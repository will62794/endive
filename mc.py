"""
Various utilities for model checking TLA+ specs with TLC and/or Apalache.
"""
import subprocess
import logging
import os
import sys
import random
import re
import tempfile
# import pyeda
# import pyeda.inter
import uuid
import itertools
import time

from itertools import chain, combinations

TLC_MAX_SET_SIZE = 10 ** 8

def mean(lst):
    return sum(lst) / len(lst)

def median(lst):
    n = len(lst)
    s = sorted(lst)
    return (s[n//2] + s[~n//2]) / 2

def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))


def pred_symmetry_reduction(invs, quant_vars):
    """ Takes a set of predicates and removes those which are equivalent under symmetry to other invariants. """
    # For now, only do symmetry reduction for exactly two quantified vars.
    if not len(quant_vars)==2:
        return invs
    qv1 = quant_vars[0]
    qv2 = quant_vars[1]
    inv_uniq_set = set()
    for inv in invs:
        swap_inv = inv
        swap_inv = swap_inv.replace(qv1, "__QV1_TEMP").replace(qv2, "__QV2_TEMP")
        swap_inv = swap_inv.replace("__QV1_TEMP", qv2).replace("__QV2_TEMP", qv1)
        # print("orig",inv)
        # print("swap",swap_inv)
        if (inv in inv_uniq_set) or (swap_inv in inv_uniq_set):
            continue
        else:
            inv_uniq_set.add(inv)
    return inv_uniq_set

def symb_equivalence_reduction(invs, invs_symb):
    """ 
    Reduce set of invariant candidates to those that are logically equivalent,
    using CNF based equivalence checking, where 'invs_symb' are symbolic version
    of the string predicates given in 'invs'. Returns the reduced set of
    invariant predicates.
    """
    # Ensure we return invariants in a consistent order i.e. avoid nondeterminism
    # of using a set here.
    invs_unique = []
    symb_invs_unique = []
    cnf_invs_set = set()
    start = time.time()
    for invi,inv in enumerate(invs):
        symb_inv = invs_symb[invi]

        # symb_min, = pyeda.inter.espresso_exprs(symb_inv.to_dnf())
        # print("ESPRESSO:", symb_min)

        # cnf_str = str(symb_inv.to_cnf())
        cnf_str = str(symb_inv.to_cnf())
        # print(cnf_str)

        # Generate and print truth table.
        # tt_expr1 = pyeda.inter.expr2truthtable(symb_min)
        # print(tt_expr1)
        
        fast_equiv_checking = True

        if fast_equiv_checking:
            # Only add predicate if there is not an equivalent one that already exists.
            if cnf_str not in cnf_invs_set:
                invs_unique.append(inv)
                cnf_invs_set.add(cnf_str)
                symb_invs_unique.append(symb_inv)
        else:
            # Potentially slower, but complete equivalence checking.
            exists_equiv = False
            for s in symb_invs_unique:
                if symb_inv.equivalent(s):
                    exists_equiv = True
                    break
            if not exists_equiv:
                invs_unique.append(inv)
                cnf_invs_set.add(cnf_str)
                symb_invs_unique.append(symb_inv)

    # Experimental checks for implication relations between predicates.
    num_implication_orderings = 0
    check_implication_relations = False
    if check_implication_relations:
        for invi,inv in enumerate(invs):
            symb_inv = invs_symb[invi]
            for invi2,inv2 in enumerate(invs):
                symb_inv2 = invs_symb[invi2]
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
    # print("symb inv unique:", len(symb_invs_unique))
    print("symb inv unique:", len(invs_unique))
    print(f"time to perform symb equiv reduction: {time.time() - start:.2f}")
    return {"invs": invs_unique, "invs_symb": symb_invs_unique}

class PredExpr():
    """ A boolean expression over a set of predicates.
    
    Represent these internally as pyeda expressions. By operating on the AST
    we can also convert these expressions to various other formats.
    """
    def __init__(self, expr):
        self.expr = expr
    # TODO.
    
    def transform_ast(ast, subst_rules):
        print(ast)

    def to_tla_expr(self):
        ast = self.expr.to_ast()
        # TODO.
        return

def pyeda_rand_pred(preds, num_terms=2):
    """ Generate a random predicate expression with the given number of variables. """
    
    # Pick some random number of remaining terms.
    if num_terms == 0:
        # Neutral term when using only disjunction ops.
        return pyeda.inter.expr(False)
    
    # End with terminal.
    if num_terms == 1:  
        p = pyeda.inter.expr(random.choice(preds))
        if random.choice([True, False]):
            p = pyeda.inter.Not(p)
        return p
    
    # Extend.
    if num_terms >= 2:
        # If we have exactly two terms left, then we must give 1 terminal
        # to each branch.
        if num_terms == 2:
            l_terms_to_use = 1
            r_terms_to_use = 1
        else:
            l_terms_to_use = random.randint(0, num_terms)
            r_terms_to_use = random.randint(0, num_terms - l_terms_to_use)

        # Build the binary expression with each branch.
        out = pyeda.inter.Or(
                pyeda_rand_pred(preds, num_terms=l_terms_to_use),
                pyeda_rand_pred(preds, num_terms=r_terms_to_use))
        # Optionally negate.
        if random.choice([True, False]):
            out = pyeda.inter.Not(out)
        return out

def generate_all_exprs(preds, num_terms=2):
    """ Generate a all predicate pyeda expressions with the given number of variables. """
    
    # Pick some random number of remaining terms.
    if num_terms == 0:
        # Neutral term when using only disjunction ops.
        return [pyeda.inter.expr(False)]
    
    # End with terminal.
    if num_terms == 1:  
        pos = [pyeda.inter.expr(p) for p in preds]
        neg = [pyeda.inter.Not(pyeda.inter.expr(p)) for p in preds]
        return pos + neg
        # p = pyeda.inter.expr(random.choice(preds))
        # if random.choice([True, False]):
        #     p = pyeda.inter.Not(p)
        # return p
    
    # Extend.
    if num_terms >= 2:
        # If we have exactly two terms left, then we must give 1 terminal
        # to each branch.
        if num_terms == 2:
            l_terms_to_use = 1
            r_terms_to_use = 1

            left = generate_all_exprs(preds, num_terms=l_terms_to_use)
            right = generate_all_exprs(preds, num_terms=r_terms_to_use)
            pos = [pyeda.inter.Or(left,right) for (left,right) in itertools.product(left,right)]
            neg = [pyeda.inter.Not(pyeda.inter.Or(left,right)) for (left,right) in itertools.product(left,right)]
            return pos + neg

        else:
            #
            # TODO: Finish this properly.
            #

            # Explore all left/right splits that sum to remaining terms allowed.
            terms_to_use = [(l,r) for (l,r) in itertools.product(range(num_terms+1),range(num_terms+1)) if l+r == num_terms]
            # l_terms_to_use = random.randint(0, num_terms)
            # r_terms_to_use = random.randint(0, num_terms - l_terms_to_use)

            # Build the binary expression for each branch.
            branches = [(generate_all_exprs(preds, num_terms=l),generate_all_exprs(preds, num_terms=r)) for (l,r) in terms_to_use]
            pos = [pyeda.inter.Or(l,r) for (l,r) in branches]
            neg = []
            # neg = [pyeda.inter.Not(pyeda.inter.Or(
            #         generate_all_exprs(preds, num_terms=l),
            #         generate_all_exprs(preds, num_terms=r)))
            #         for (l,r) in terms_to_use]
            return pos + neg

def compute_subsumption_ordering(invs, num_samples_to_check=None):
    """ 
    Compute graph of subsumption partial order between given set of invariants/predicates.
    
    Assumes invariants are given as pyeda expressions.
    """
    num_implication_orderings = 0
    edges = []
    ind_edges = []
    # If A => B, then we only need to check A, since B is weaker than A.
    redundant = set()
    now = time.time()
    # Limit cost of these checks with some limiting.
    sampled_inds = list(range(len(invs)))
    if num_samples_to_check is not None:
        sampled_inds = random.sample(range(len(invs)), num_samples_to_check)
    for invi,inv in enumerate(invs):
        if invi not in sampled_inds:
            continue
        symb_inv = inv

        for invi2,inv2 in enumerate(invs):
            if invi == invi2:
                continue
            symb_inv2 = inv2
            # pyeda.inter.expr(inv2)
            impliesforward = pyeda.inter.Implies(symb_inv, symb_inv2, simplify=True)
            # impliesback = pyeda.inter.Implies(symb_inv2, symb_inv, simplify=True)
            
            # comparing Or(~x_017, ~x_000, x_013) and Or(x_007, x_016, ~x_011)
            # print(f"comparing {symb_inv} => {symb_inv2}")
            # print("  implies:", impliesforward)
            # print("  implies:", impliesback)

            if impliesforward.equivalent(True) and (not invi2 == invi):
                # print(f"comparing {symb_inv} => {symb_inv2}")
                num_implication_orderings += 1
                edges.append((symb_inv, symb_inv2))
                ind_edges.append((invi, invi2))
                redundant.add(invi)

            # if impliesback.equivalent(True) and not impliesforward.equivalent(True):
            #     # print(f"comparing {symb_inv} <= {symb_inv2}")
            #     # print("  implies:", impliesback)
            #     num_implication_orderings += 1
            #     edges.append((symb_inv2, symb_inv))
            #     ind_edges.append((invi2, invi))

    print("subsumption checks took {:.2f}s:".format(time.time()-now))
    print("redundant:", len(redundant))
    return (ind_edges,edges,redundant)
   
def generate_invs(preds, num_invs, min_num_conjuncts=2, max_num_conjuncts=2, 
                    process_local=False, boolean_style="tla", quant_vars=[], use_pred_identifiers=False,
                    invs_avoid_set=set(),
                    pred_weights=None):
    """ Generate 'num_invs' random invariants with the specified number of conjuncts. """
    # Pick some random conjunct.
    # OR and negations should be functionally complete
    symb_neg_op = "~"
    if boolean_style == "cpp":
        # ops = ["&&", "||"]
        ops = ["||"]
        andop = "&&"
        neg_op = "!"
    elif boolean_style == "pyeda":
        # TODO: Python vs. pyeda syntax?
        # ops = ["|"]
        ops = ["or"]
        andop = "&"
        # neg_op = "~"
        neg_op = "not"
    elif boolean_style == "tla":
        # ops = ["/\\", "\\/"]
        ops = ["\\/"]
        andop = "/\\"
        neg_op = "~"

    # Assign a numeric id to each predicate.
    pred_id = {p:k for (k,p) in enumerate(preds)}

    weights_by_pred = {}
    if pred_weights is not None:
        weights_by_pred = {p:pred_weights[ind] for ind,p in enumerate(preds)}

    def select_next_conjunct_ind(conjs):
        # Select next conjunct, weighting appropriately if specified.
        if pred_weights is not None:
            conjunct_weights = [weights_by_pred[c] for ind,c in enumerate(conjs)]
            cind = random.choices(range(len(conjs)), weights=conjunct_weights, k=1)[0]
        else:
            cind = random.randint(0, len(conjs)-1)
        return cind        

    start = time.time()
    invs = []
    invs_set = set()
    invs_symb = []
    invs_symb_strs = []
    total_gen_dur = 0
    total_check_dur = 0
    enable_symb_equiv_reduction = False
    for invi in range(num_invs):
        conjuncts = list(preds)
        # conjuncts = list(map(str, range(len(preds))))
        num_conjuncts = random.randint(min_num_conjuncts, max_num_conjuncts)
        
        # Select first atomic term of overall predicate.
        cind = select_next_conjunct_ind(conjuncts)
        # cind = random.randint(0, len(conjuncts)-1)
        c = conjuncts[cind]
        conjuncts.remove(c)

        # Optionally negate it.
        negate = random.choice([True, False])
        (n,fn) = (neg_op,symb_neg_op) if negate else ("","")

        inv = n + "(" + c + ")"
        # Use only the identifier of the predicate in the overall expression,
        # rather than the actual predicate expression itself.
        if use_pred_identifiers:
            inv = n + "(" + f"PRED_{cind}" + ")"

        pred_id_var = f"x_{str(pred_id[c]).zfill(3)}"
        symb_inv_str = fn + "(" + pred_id_var + ")"

        total_gen_dur_start = time.time()
        for i in range(1,num_conjuncts):
            if len(conjuncts) == 0:
                break
            # # Select next conjunct, weighting appropriately if specified.
            # if pred_weights is not None:
            #     conjunct_weights = [weights_by_pred[c] for ind,c in enumerate(conjuncts)]
            #     cind = random.choices(range(len(conjuncts)), weights=conjunct_weights, k=1)[0]
            # else:
            #     cind = random.randint(0, len(conjuncts)-1)
            cind = select_next_conjunct_ind(conjuncts)

            c = conjuncts[cind]
            conjuncts.remove(c)
            op = ""
            fop = "|"
            if i < num_conjuncts:
                op = random.choice(ops)
            negate = random.choice([True, False])
            (n,fn) = (neg_op,symb_neg_op) if negate else ("","")
            new_term = n + "(" + c + ")"
            # Use only the identifier of the predicate in the overall expression.
            if use_pred_identifiers:
                new_term = n + "(" + f"PRED_{cind}" + ")"

            # Sort invariant terms to produce more consistent output regardless of random seed.
            new_inv_args = [new_term,inv]
            # TODO: Generalize this so that whole expressions can be negated?
            use_restricted_negation = True
            front_neg = random.choice(["", "~"])
            if use_restricted_negation:
                front_neg = random.choice([""]) # less general but possibly more compact/efficient in practice.
                new_inv_args = sorted(new_inv_args) # With generalized negation structure don't think we want sorting here.

            inv  =  new_inv_args[0] + " " + op + " " + front_neg + "(" + new_inv_args[1] +")"

            # inv  =  n + "(" + c + ")" + " " + op + " (" + inv +")"
            
            # Symbolic version of the predicate. Used for quickly 
            # detecting logically equivalent predicate forms.
            pred_id_var = f"x_{str(pred_id[c]).zfill(3)}"
            symb_inv_str = fn + "(" + pred_id_var + ")" + " " + fop + " " + front_neg + "(" + symb_inv_str +")"
        total_gen_dur += time.time() - total_gen_dur_start

        total_check_start = time.time()
        # if inv not in invs:
        # Use more efficient set lookup here to check against.
        if inv not in invs_set and (symb_inv_str not in invs_avoid_set):
            # print(inv)
            # Don't add tautologies or contradictions.
            # if not symb_expr.equivalent(True) and not symb_expr.equivalent(False):
            invs.append(inv)
            invs_set.add(inv)
            invs_symb_strs.append(symb_inv_str)

            if enable_symb_equiv_reduction:
                import pyeda.inter
                symb_expr = pyeda.inter.expr(symb_inv_str)
                invs_symb.append(symb_expr)
        total_check_dur += time.time() - total_check_start

            # print(symb_inv_str)
            # print(type(invs_symb[-1]))

    logging.info(f"number of invs: {len(invs)}")
    logging.info(f"time to generate {len(invs)} invs: {time.time()-start:.2f} secs.")
    logging.info(f"time to generate {len(invs)} invs (gendir): {total_gen_dur:.2f} secs.")
    logging.info(f"time to generate {len(invs)} invs (checkdir): {total_check_dur:.2f} secs.")

    # Do CNF based equivalence reduction.
    if enable_symb_equiv_reduction:
        res = symb_equivalence_reduction(invs, invs_symb)
        invs = res["invs"]
        invs_symb_strs = res["invs_symb"]
        logging.info(f"number of invs post CNF based equivalence reduction: {len(invs)}")

    # if len(quant_vars):
        # invs = pred_symmetry_reduction(invs, quant_vars)
    logging.info(f"number of post symmetry invs: {len(invs)}")

    # return invs_symb
    # return invs_symb_strs
    # return set(map(str, invs_symb))
    return {"raw_invs": set(invs), "pred_invs": invs_symb_strs}

def greplines(pattern, lines):
    return [ln for ln in lines if re.search(pattern, ln)]

def runtlc(spec,config=None,tlc_workers=6,cwd=None,tlcjar="tla2tools-checkall.jar",java="java",tlc_flags="", 
           max_depth=2**30, 
           cache_with_ignored=None, 
           cache_with_ignore_inv_counts=None,
           cache_state_load=False,
           recache_seed_set=None):
    # Make a best effort to attempt to avoid collisions between different
    # instances of TLC running on the same machine.
    dirpath = tempfile.mkdtemp()
    metadir_path = f"states/states_{uuid.uuid4().hex[:16]}"
    cacheFlags = ""
    if (cache_with_ignored is not None) and (not cache_state_load):
        cacheFlags = f"-cacheStates cache"
    if cache_state_load:
        cacheFlags = f"-cacheStates load"

    if recache_seed_set is not None:
        recache_set_str = ",".join(recache_seed_set)
        cacheFlags = f"-cacheStates recache \"{recache_set_str}\""

    if cache_with_ignored is not None:
        # Ignored var sets are specified in the command line arg like: v1,v2|v1,v3,v4|v1,v5
        cacheWithIgnoredVarSets = "|".join([",".join(cvars) for cvars in cache_with_ignored])
        cacheFlags += f' -cacheStatesIgnoreVars "{cacheWithIgnoredVarSets}"'
        if cache_with_ignore_inv_counts is not None:
            cacheWithIgnoredInvCounts = "|".join([str(c) for c in cache_with_ignore_inv_counts])
            cacheFlags += f' -cacheStatesIgnoreVarsInvListCounts "{cacheWithIgnoredInvCounts}"'

    cmd = java + (f' -XX:+UseParallelGC -Djava.io.tmpdir="{dirpath}" -cp {tlcjar} tlc2.TLC {tlc_flags} {cacheFlags} -maxDepth {max_depth} -maxSetSize {TLC_MAX_SET_SIZE} -metadir {metadir_path} -noGenerateSpecTE -checkAllInvariants -deadlock -continue -workers {tlc_workers}')
    if config:
        cmd += " -config " + config
    cmd += " " + spec
    logging.debug("TLC command: " + cmd)
    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=cwd)
    tlc_raw_out = ""
    line_str = ""
    tlc_lines = []
    while True:
        new_stdout = subproc.stdout.read(1).decode(sys.stdout.encoding)
        if new_stdout == "": # reached end of file.
            break
        if new_stdout == os.linesep:
            # logging.debug("[TLC Output] " + line_str)
            tlc_lines.append(line_str)
            line_str = ""
        else:
            line_str += new_stdout
    # check exit code of subproc.
    retcode = subproc.wait()

    # logging.info("++++++++++++++++++++++")
    # for last in tlc_lines[-28:]:
        # logging.info(last)
    # logging.info("++++++++++++++++++++++")
    
    if retcode != 0 and retcode != 255:
        logging.error(f"!!!!!!!! TLC exited with non-zero exit code: {retcode}. May indicate underlying error. !!!!!!!!")
        logging.error("Logging last 25 lines of TLC output:")
        logging.error("------")
        for last in tlc_lines[-25:]:
            logging.error(last)
        logging.error("------")
        raise Exception(f"TLC exited with non-zero exit code: {retcode}.")
    return tlc_lines

# Run TLC on spec to check all invariants and return the set 
# of invariants that were violated.
def runtlc_check_violated_invariants(spec,config=None, tlc_workers=6, cwd=None, tlcjar="tla2tools-checkall.jar", java="java", 
                                     max_depth=2**30, 
                                     cache_with_ignored=None, 
                                     cache_with_ignore_inv_counts=None,
                                     cache_state_load=False, tlc_flags="",
                                     recache_seed_set=None):
    #
    # TODO: Check for this type of error:
    # 'Error: The invariant of Inv91 is equal to FALSE'
    #
    lines = runtlc(spec,config=config,tlc_workers=tlc_workers,cwd=cwd,tlcjar=tlcjar, 
                    java=java, max_depth=max_depth, 
                    cache_with_ignored=cache_with_ignored, 
                    cache_with_ignore_inv_counts=cache_with_ignore_inv_counts,
                    cache_state_load=cache_state_load, tlc_flags=tlc_flags,
                    recache_seed_set=recache_seed_set)
    invs_violated = set()
    for l in greplines("is violated", lines):
        res = re.match(".*Invariant (Inv.*) is violated",l)
        invname = res.group(1)
        invs_violated.add(invname)
    slice_sizes = []
    slice_stats = []
    for l in greplines("Slice.*total unique", lines):
        res = re.match("Slice_(.*) (.*) -> total unique cached states. (.*)",l)
        slice_ind = res.group(1)
        slice_ignore_vars = sorted(res.group(2).split(","))
        slice_size = int(res.group(3))
        # print("slice_stats:", slice_ind, slice_ignore_vars, slice_size)
        slice_sizes.append(slice_size)
        slice_stats.append((slice_ind, slice_ignore_vars, slice_size))
    return {
        "invs_violated": invs_violated,
        "slice_stats": slice_stats
    }


class State():
    """ A single TLA+ state. """
    def __init__(self, state_str="", state_lines=[], load_from_obj=None):
        self.state_str = state_str
        self.state_lines = state_lines
        if load_from_obj:
            self.load_from(load_from_obj)

    def __str__(self):
        return self.state_str

    def pretty_str(self):
        out = ""
        for l in self.state_lines:
            out += l + "\n"
        return out
    
    def serialize(self):
        ret = {
            "state_str": self.state_str,
            "state_lines": self.state_lines
        }
        if hasattr(self, "state_lines_action_vars_projected"):
            ret["state_lines_action_vars_projected"] = self.state_lines_action_vars_projected
        if hasattr(self, "state_var_projection_map"):
            ret["state_var_projection_map"] = self.state_var_projection_map
        return ret
    
    def load_from(self, obj):
        self.state_str = (obj["state_str"])
        self.state_lines = (obj["state_lines"])

class Trace():
    """ Represents a trace of states. """
    def __init__(self, states):
        # List of states.
        self.states = states

    def getStates(self):
        return self.states
    
    def serialize(self):
        return [s.serialize() for s in self.states]

class CTI():
    """ Represents a single counterexample to induction (CTI) state. """
    def __init__(self, cti_str="", cti_lines=[], action_name="", inv_name="", trace=None, load_from_obj=None):
        self.cti_str = cti_str
        self.action_name = action_name
        self.inv_name = inv_name
        self.cti_lines = cti_lines
        # The full counterexample trace associated with this CTI. The CTI state may fall at 
        # different points within this trace.
        self.trace = trace

        # Optional cost metric for this CTI
        self.cost = 0

        self.trace_index = -1

        if load_from_obj:
            self.load_from(load_from_obj)

    def var_vals(self):
        vals = {}
        for cti_line in self.cti_lines:
            # Remove the conjunction (/\) at the beginning of the line.
            cti_line = cti_line[2:].strip()
            # Look for the first equals sign.
            first_equals = cti_line.index("=")
            varname = cti_line[:first_equals].strip()
            varval = cti_line[first_equals+1:]
            vals[varname] = varval
        return vals

    def set_var_val(self, varname, new_var_str):
        """ Update the value of a variable in the CTI with a string representing a TLA+ expression. """
        # Update the CTI lines.
        vals = self.var_vals()
        if varname in vals:
            vals[varname] = new_var_str
        self.cti_lines = [f"/\\ {v} = {vals[v]}" for v in vals]
        self.cti_str = " /\\ ".join(self.cti_lines)

    def serialize(self):
        ret = {
            "cti_str": self.cti_str,
            "action_name": self.action_name,
            "cti_lines": self.cti_lines,
            "trace": [s.serialize() for s in self.trace.getStates()],
            "cost": self.cost,
            "hashId": str(hash(self))
        }

        if hasattr(self, "cti_lines_action_vars_projected"):
            ret["cti_lines_action_vars_projected"] = self.cti_lines_action_vars_projected
        return ret
    
    def load_from(self, obj):
        self.cti_str = obj["cti_str"]
        self.action_name = obj["action_name"]
        self.cti_lines = obj["cti_lines"]
        self.trace = Trace([State(load_from_obj=s) for s in obj["trace"]])

    def getCTIStateString(self):
        return self.cti_str

    def getPrimedCTIStateString(self):
        """ Return CTI as TLA+ state string where variables are primed."""
        primed_state_vars = []
        for cti_line in self.cti_lines:
            # Remove the conjunction (/\) at the beginning of the line.
            cti_line = cti_line[2:].strip()
            # print(cti_line)
            # Look for the first equals sign.
            first_equals = cti_line.index("=")
            varname = cti_line[:first_equals].strip()
            varval = cti_line[first_equals+1:]
            # print("varname:", varname)
            # print("varval:", varval)
            primed_state_vars.append(f"/\\ {varname}' ={varval}")
        primed_state = " ".join(primed_state_vars)
        # print(primed_state)
        return primed_state
    
    def getActionName(self):
        return self.action_name
    
    def setActionName(self, action_name):
        self.action_name = action_name

    def setInvName(self, inv_name):
        self.inv_name = inv_name

    def setTrace(self, trace):
        self.trace = trace

    def getTrace(self):
        return self.trace

    def pretty_str(self):
        out = ""
        for l in self.cti_lines:
            out += l + "\n"
        return out
            

    def __hash__(self):
        return hash(self.cti_str)
    
    def __eq__(self, other):
        return hash(self.cti_str) == hash(other.cti_str)
    
    def __str__(self):
        return self.cti_str
    
    # Order CTIs as strings.
    def __lt__(self, other):
        return self.cti_str < other.cti_str


class Apalache:
    """ Utilities for model checking TLA+ with Apalache. """
    def __init__(self, specdir) -> None:
        self.apalache_bin = "apalache/bin/apalache-mc"
        self.specdir = specdir
        self.GEN_TLA_DIR = "gen_tla" # TODO: pass this in.

    def gen_check_spec(self, orig_spec_name, check_spec_name, defs):
        """ 
        Create a spec that allows for various model checking tasks.

        Adds all given 'defs' as new definitions in a spec that extends the given original spec. Expects
        'defs' to be given as a map from definition names to TLA+ expressions.
        """
        
        # Build the spec.
        spec_lines = [
            "---- MODULE %s ----\n" % check_spec_name,
            f"EXTENDS {orig_spec_name},Naturals,TLC\n"
        ] + [
            f"{d} == {defs[d]}" for d in defs
        ] + [
            "===="
        ]
        return "\n".join(spec_lines)

    def check(self, orig_spec_name, init, inv, defs={}, length=1):
        # Clean the output directory.
        os.system("rm -rf benchmarks/gen_tla/apalache-cti-out")

        check_spec_name = f"{orig_spec_name}_ApaCheck"
        spec_text = self.gen_check_spec(orig_spec_name, check_spec_name, defs)
        tla_file = f"{os.path.join(self.specdir, self.GEN_TLA_DIR)}/{check_spec_name}.tla"
        tla_filename = f"{self.GEN_TLA_DIR}/{check_spec_name}.tla"

        f = open(tla_file, 'w')
        f.write(spec_text)
        f.close()

        rundir = "gen_tla/apalache_ctigen"
        outdir = "gen_tla/apalache_ctigen"
        jvm_args="JVM_ARGS='-Xss16M'"
        args = [
            f"--out-dir={outdir}",
            f"--run-dir={rundir}",
            # f"--max-error={max_num_ctis}",
            # f"--view=vars",
            f"--cinit=CInit",
            f"--init={init}",
            f"--next=Next",
            f"--inv={inv}",
            f"--length={length}",
            tla_filename
        ]
        cmd = f"{self.apalache_bin} check {' '.join(args)}"
        logging.debug("Apalache command: " + cmd)
        workdir = None
        if self.specdir != "":
            workdir = self.specdir
        subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=workdir)
        return subproc
    
    def await_output(self, apalache_subproc):
        apa_out = apalache_subproc.stdout.read().decode(sys.stdout.encoding)
        lines = [x.strip() for x in apa_out.splitlines()]
        # Check for successful Apalache run.
        for l in lines:
            if "Checker reports no error up to computation length 1" in l:
                return {"error":False, "stdout": apa_out}
        return {"error":True, "stdout": apa_out}

    def compute_minimal_support_graph(self, orig_spec_name, defs, typeok, inductive_inv):
        """ 
        Computes the minimal support graph for the given inductive invariant passed as a list of lemmas given
        as (name, expr) pairs.
        """
        logging.info(f"Computing minimal support graph for inductive invariant: {inductive_inv}")
        support_sets = {}
        lemma_subsets = powerset(inductive_inv)
        lemma_subsets_by_size = [[s for s in lemma_subsets if len(s) == size] for size in range(len(inductive_inv))]
        for lemma_name in inductive_inv:
            logging.info(f"Computing support graph for lemma: {lemma_name}")
            # TODO: Use binary search for computing support sets more efficiently?
            for support_lemmas in powerset(inductive_inv):
                if lemma_name not in support_lemmas:
                    # Only need to check support sets that include ourself.
                    continue
                    
                logging.info(f"Checking support set {support_lemmas}, for lemma {lemma_name}")
                defs["IndCheck"] = "\n  /\\ " + " \n  /\\ ".join([typeok] + [name for name in support_lemmas])
                
                # Check induction of current lemma relative to subsets of other lemmas.
                subproc = self.check(orig_spec_name, "IndCheck", lemma_name, defs = defs, length=1)
                res = self.await_output(subproc)
                # print(res["error"])
                # print(res["stdout"])
                if not res["error"]:
                    # Found valid support set.
                    logging.info(f"Found support set: {support_lemmas}, lemma: {lemma_name}")
                    support_sets[lemma_name] = support_lemmas
                    # Finish and move on to next lemma.
                    break

if __name__ == "__main__":
    log_level = logging.DEBUG
    log_format = '%(message)s'
    logging.basicConfig(stream=sys.stdout, format=log_format, filemode='w', level=log_level)


    #
    # Testing some Apalache class features.
    #
    specname = "TwoPhase"
    typeok = "TypeOK"
    logging.info("Doing final inductive check with Apalache.")

    strengthening_conjuncts = [
        ("A_Inv89_1_0_def" , '\A rmi \in RM : ([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(tmPrepared = tmPrepared \cup {rmi}))'),
        ("A_Inv326_1_1_def" , '(tmPrepared = RM) \/ (~([type |-> "Commit"] \in msgsAbortCommit))'),
        ( "A_Inv51_1_2_def" , '\A rmi \in RM : ([type |-> "Commit"] \in msgsAbortCommit) \/ (~(rmState[rmi] = "committed"))'),
        ("A_Inv446_1_3_def" , '\A rmi \in RM : ~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared) \/ (~(rmState[rmi] = "working"))'),
        ( "A_Inv380_1_4_def" , '(tmState = "committed") \/ (~([type |-> "Commit"] \in msgsAbortCommit))'),
        ("A_Inv362_1_5_def", '(tmState = "aborted") \/ (~([type |-> "Abort"] \in msgsAbortCommit))'),
        ( "A_Inv479_1_6_def" , '\A rmi \in RM : ~(rmState[rmi] = "aborted") \/ (~(tmState = "committed"))'),
        ("A_Inv2450_2_7_def" , '\A rmi \in RM : (rmState[rmi] = "prepared") \/ (~(tmPrepared = tmPrepared \cup {rmi})) \/ (~(tmState = "init"))'),
        ("A_Inv115_1_0_def" , '\A rmj \in RM : ([type |-> "Prepared", rm |-> rmj] \in msgsPrepared) \/ (~(rmState[rmj] = "prepared"))'),
        ("A_Inv339_1_1_def" , '(tmPrepared = RM) \/ (~(tmState = "committed"))'),
        ("A_Inv2469_2_2_def" , '\A rmi \in RM : (rmState[rmi] = "prepared") \/ (~(tmState = "init")) \/ (~([type |-> "Prepared", rm |-> rmi] \in msgsPrepared))')
    ]

    lemmas = [("Safety","TCConsistent")] + strengthening_conjuncts
    defs = {name:exp for name,exp in lemmas}
    defs["IndCurr"] = f"\n  /\\ {typeok} \n  /\\ " +  " \n  /\\ ".join([name for name,exp in lemmas])
    # Check induction step.
    apalache = Apalache("benchmarks")
    apa_subproc = apalache.check("TwoPhase", "IndCurr", "IndCurr", defs = defs, length=1)
    res = apalache.await_output(apa_subproc)
    logging.debug(res["stdout"])
    if not res["error"]:
        logging.info("Apalache final induction check: PASS!")

        # Try computing minimal support graph.
        inductive_inv = ["Safety"] + [c[0] for c in strengthening_conjuncts] 
        apalache.compute_minimal_support_graph(specname, defs, typeok, inductive_inv)
    else:
        logging.info("Apalache final induction check: FAIL (not truly inductive)")