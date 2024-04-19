#!/bin/bash
specname_arg=$1

lscpu # log CPU info.
echo "Loading Java"
module load OpenJDK/19.0.1

# Create work directory.
bmdir="/scratch/schultz.w/benchmarking/$specname_arg"
mkdir -p $bmdir
cd $bmdir

# Clone if not already cloned.
git clone --depth 1 -b ind-tree https://github.com/will62794/endive.git
cd endive
git pull --rebase
python3 -m pip install -r requirements.txt

# Clean up old files.
rm -rf benchmarks/statecache
rm -rf benchmarks/states

#
# Common parameters for benchmarking runs.
#

tlc_workers=24
num_ctigen_workers=8
cti_elimination_workers=1

nrounds=45
ninvs=200000
max_num_ctis_per_round=500
target_sample_states=200000
num_simulate_traces=200000
niters=5

common_flags=" --tlc_workers $tlc_workers --num_ctigen_workers $num_ctigen_workers --cti_elimination_workers=$cti_elimination_workers"
common_flags+=" --debug --target_sample_time_limit_ms 10000 --num_simulate_traces $num_simulate_traces --target_sample_states $target_sample_states"
common_flags+=" --opt_quant_minimize --k_cti_induction_depth 1"
common_flags+=" --ninvs $ninvs --max_num_ctis_per_round $max_num_ctis_per_round"
common_flags+=" --save_dot --max_num_conjuncts_per_round 20 --niters $niters --nrounds $nrounds"

time_limit_large="08:00:00"
