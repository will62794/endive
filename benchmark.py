import time
import logging
import csv

from endive import *

benchmark_dir = "benchmarks"

# (benchmark-id, specname, opt_quant_minimize, default_seed)
benchmark_specs = [
    ("tla-consensus", "Consensus", True, 13),
    ("tla-tcommit", "TCommit", True, 10),
    ("i4-lock-server", "lockserver", True, 13),
    ("ex-quorum-leader-election", "quorum_leader_election", False, 10),
    ("pyv-toy-consensus-forall", "toy_consensus_forall", False, 12),
    ("tla-simple", "Simple", True, 12),
    ("ex-lockserv-automaton", "lockserv_automaton", True, 10),
    ("tla-simpleregular", "SimpleRegular", True, 10),
    ("pyv-sharded-kv", "sharded_kv", True, 11),
    ("pyv-lockserv", "lockserv", True, 10),
    ("tla-twophase", "TwoPhase", True, 11),
    ("i4-learning-switch", None, True, None), #"learning_switch")
    ("ex-simple-decentralized-lock", "simple_decentralized_lock", True, 10),
    ("i4-two-phase-commit", "two_phase_commit", True, 11),
    ("pyv-consensus-wo-decide", "consensus_wo_decide", True, 10),
    ("pyv-consensus-forall", "consensus_forall", True, 13),
    ("pyv-learning-switch", None, True, None), # "learning_switch"),
    ("i4-chord-ring-maintenance", None, True, None), # "")
    ("pyv-sharded-kv-no-lost-keys", "sharded_kv_no_lost_keys", True, 10),
    ("ex-naive-consensus", "naive_consensus", True, 13),
    ("pyv-client-server-ae", "client_server_ae", True, 13),
    ("ex-simple-election", "simple_election", True, 12),
    ("pyv-toy-consensus-epr", "toy_consensus_epr", True, 11),
    ("ex-toy-consensus", "toy_consensus", False, 12),
    ("pyv-client-server-db-ae", "client_server_db_ae", True, 21),
    ("pyv-hybrid-reliable-broadcast", None, True, None),
    ("pyv-firewall", "firewall", False, 10),
    ("ex-majorityset-leader-election", "majorityset_leader_election", True, 11),
    ("pyv-consensus-epr", "consensus_epr", True, 13),
    ("mongo-logless-reconfig", "MongoLoglessDynamicRaft", True, 12) # TODO: update default seed.
]

if __name__ == "__main__":
    DEFAULT_TLC_WORKERS = 6
    DEFAULT_NUM_SEEDS = 1
    DEFAULT_INIT_SEED = 10
    DEFAULT_JAVA_EXE = "java -Xss4M"

    parser = argparse.ArgumentParser(description='')
    parser.add_argument('--name', help='Benchmarks to run.', default=None, required=False, type=str)
    parser.add_argument('--tlc_workers', help='Number of TLC workers to use.', required=False, type=int, default=DEFAULT_TLC_WORKERS)
    parser.add_argument('--nseediters', help='Number of random seeds to test for each benchmark.', required=False, type=int, default=DEFAULT_NUM_SEEDS)
    parser.add_argument('--init_seed', help='Initial random seed.', required=False, type=int, default=DEFAULT_INIT_SEED)
    parser.add_argument('--results_dir', help='Directory to save results.', required=False, type=str, default="results")
    parser.add_argument('--java_exe', help='Java executable.', required=False, type=str, default=DEFAULT_JAVA_EXE)
    parser.add_argument('--fastest', help='Whether to save only the fastest benchmark run.', required=False, action='store_true', default=False)
    parser.add_argument('--fmcad22', help='For reproducing results from FMCAD 2022 paper.', required=False, action='store_true', default=False)

    args = vars(parser.parse_args())

    # Initialize logging.
    logfile = 'benchmarks.log'
    log_format = '%(message)s'
    logging.basicConfig(filename=logfile, format=log_format, filemode='w', level=logging.INFO)

    results = []

    print(f"{len(benchmark_specs)} total benchmarks.")
    if args["fmcad22"]:
        print(f"Setting parameters from FMCAD 2022 paper, to ensure reproducibility.")
    bench_start = time.time()

    # Run a single benchmark.
    if args["name"] is not None:
        bm_names = args["name"].split(",")
        print(f"Running specified benchmarks: {bm_names}")
        benchmark_specs = [bm for bm in benchmark_specs if bm[0] in bm_names]

    for (benchmark_id,specname,opt_quant_minimize,default_seed) in benchmark_specs:
        if specname is None:
            result = (benchmark_id, False, 0, "n/a")
            results.append(result)
            continue

        benchmark_tstart = time.time()

        # Set Java binary path.
        JAVA_EXE = args["java_exe"]
        spec_config_file = os.path.join(benchmark_dir, specname) + ".config.json"
        fcfg = open(spec_config_file)
        spec_config = json.load(fcfg)

        # Load config parameters.
        preds = spec_config["preds"]
        preds_alt = spec_config["preds_alt"]    
        safety = spec_config["safety"]
        constants = spec_config["constants"]
        constraint = spec_config["constraint"]
        quant_inv = spec_config["quant_inv"]
        quant_inv_alt = spec_config["quant_inv_alt"]
        quant_vars = spec_config["quant_vars"]
        model_consts = spec_config["model_consts"]
        symmetry = spec_config["symmetry"]    
        typeok = spec_config["typeok"]
        simulate = spec_config["simulate"]
        pregen_inv_cmd = spec_config.get("pregen_inv_cmd", None)
        try_final_minimize = spec_config.get("try_final_minimize", False)
        load_inv_cache = spec_config.get("load_inv_cache", None)

        num_iters = 3
        num_rounds = 4
        num_invs = 15000
        num_simulate_traces = 50000
        simulate_depth = 6
        tlc_workers = args["tlc_workers"]
        nseediters = args["nseediters"]
        init_seed = args["init_seed"]
        results_dir = args["results_dir"]

        # Random seeds for the run i.e. run each benchmark on every seed.
        if args["fmcad22"]:
            # If we are reproducing paper results, use fixed seed for consistency across runs.
            seeds = [default_seed]
        else:
            seeds = [(init_seed + i) for i in range(nseediters)]

        logstr = f"**********************************\nBenchmark: '{benchmark_id}' (specname: '{specname}')\n**********************************"
        print(logstr)
        logging.info(logstr)
        print(f"Running each benchmark over {len(seeds)} total random seeds: {list(seeds)}")
        print("")

        indgen_runs = []
        for seed in seeds:
            tstart = time.time()

            # Read pre-cached invariants from a file if specified.
            cached_invs = None
            cached_invs_gen_time_secs = None
            if load_inv_cache:
                invf = open(load_inv_cache)
                lines = invf.read().splitlines()
                cached_invs = lines[1:]
                cached_invs_gen_time_secs = int(lines[0])
                logging.info("Loaded %d cached invariants from cache file: '%s', with duration=%ds" % (len(cached_invs), load_inv_cache, cached_invs_gen_time_secs))

            print(f"- Running benchmark '{benchmark_id}' (seed {seed})")
            # Generate inductive invariant.
            indgen = InductiveInvGen(benchmark_dir, specname, safety, constants, constraint, quant_inv, model_consts, preds,
                                        num_rounds=num_rounds, num_invs=num_invs, seed=seed, typeok=typeok, num_iters=num_iters,
                                        symmetry=symmetry, simulate=simulate, simulate_depth=simulate_depth, num_simulate_traces=num_simulate_traces, 
                                        tlc_workers=tlc_workers, java_exe=JAVA_EXE, cached_invs=cached_invs, cached_invs_gen_time_secs=cached_invs_gen_time_secs, pregen_inv_cmd=pregen_inv_cmd, opt_quant_minimize=opt_quant_minimize,
                                        try_final_minimize=try_final_minimize)
            indgen.run()
            succ = indgen.is_inv_inductive()
            print(f"Discovered invariant is likely inductive? {succ}")
            if succ:
                indinv = indgen.get_inductive_inv()
                print(f"Num conjuncts in final inductive invariant: {len(indinv)}")
                print("/\\", indinv[0])
                for conj in indinv[1:]:
                    print("/\\", conj[1])
                    # print(defn, inv)

            # Save result.
            indgen_runs.append(indgen)

            print(f"CTI generation duration: {indgen.get_ctigen_duration():.2f} secs.")
            print(f"Invariant checking duration: {indgen.get_invcheck_duration():.2f} secs.")
            print(f"CTI elimination checks duration: {indgen.get_ctielimcheck_duration():.2f} secs.")

            # total_duration = (time.time() - tstart)
            print(f"Total duration: {indgen.get_total_duration():.2f} secs.")
            print("")

            # To avoid potential TLC name clashing issues between runs.
            time.sleep(1.5)

        # Optionally save only the fastest run. Otherwise, save all runs.
        if args["fastest"]:
            best_indgen = sorted(indgen_runs, key=lambda o : o.get_stats_obj()["total_duration_secs"])[0]
            print("Saving fastest benchmark run, seed=" + str(best_indgen.seed))
            best_indgen.save_result(results_dirname=results_dir)
        else:
            # Save all runs.
            for indgen_obj in indgen_runs:
                indgen_obj.save_result(results_dirname=results_dir)

        total_benchmark_duration = (time.time() - benchmark_tstart)
        print(f"Total duration of '{benchmark_id}' benchmark: {total_benchmark_duration:.2f} secs.")
        print("=================\n")

    bench_dur = time.time() - bench_start
    print(f"Total duration of all benchmarks: {bench_dur:.2f} secs.")