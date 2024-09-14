#!/bin/bash
specname_arg=$1

lscpu # log CPU info.
echo "Loading modules"
module load OpenJDK/19.0.1
module load gcc/11.1.0

#
# To optionally install TLA+ proof manager, if we want to enable this for later use.
#

# If tlapm install directory does not exist, create it.
# cd /home/schultz.w
# wget https://github.com/tlaplus/tlapm/releases/download/v1.4.5/tlaps-1.4.5-x86_64-linux-gnu-inst.bin
# chmod +x tlaps-1.4.5-x86_64-linux-gnu-inst.bin
# mkdir tlapm_install
# ./tlaps-1.4.5-x86_64-linux-gnu-inst.bin -d /home/schultz.w/tlapm_install

#
# Run with tlapm_install/bin/tlapm
#

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
num_ctigen_workers=20
cti_elimination_workers=1

nrounds=70
ninvs=1000000
max_num_ctis_per_round=800
ninvs_per_iter_group=25000
target_sample_states=200000
target_sample_time_limit_ms=150000
num_simulate_traces=200000
niters=5
tlapm_install="/home/schultz.w/tlapm_install"

common_flags=" --tlc_workers $tlc_workers --num_ctigen_workers $num_ctigen_workers --cti_elimination_workers=$cti_elimination_workers"
common_flags+=" --debug --target_sample_time_limit_ms $target_sample_time_limit_ms --num_simulate_traces $num_simulate_traces --target_sample_states $target_sample_states"
common_flags+=" --opt_quant_minimize --k_cti_induction_depth 1"
common_flags+=" --ninvs $ninvs --max_num_ctis_per_round $max_num_ctis_per_round --ninvs_per_iter_group $ninvs_per_iter_group"
common_flags+=" --save_dot --max_num_conjuncts_per_round 20 --niters $niters --nrounds $nrounds"
common_flags+=" --tlapm_install $tlapm_install --do_tlaps_induction_checks"

time_limit_large="08:00:00"
