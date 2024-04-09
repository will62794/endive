#!/bin/sh
#
# Download logs and other data from Discovery server.
#
set -e

mkdir -p discovery_data

echo "Fetching logs"
xfer="schultz.w@xfer.discovery.neu.edu"
scp -O -r $xfer:/scratch/schultz.w/endive_logs discovery_data

bmdir="/scratch/schultz.w/benchmarking"
local_dir="discovery_data/proof_graphs"
mkdir -p $local_dir

# Fetch proof graph stuff.
bms="TwoPhase consensus_epr LamportMutex Hermes ZeusReliableCommit Boulanger Bakery AsyncRaft"
# If list of arguments passed, use that instead.
if [ $# -gt 0 ]; then
    bms=$@
fi
echo "Fetching proof graphs."
for bm in $bms
do
    # Fetch rendered proof tree and proof graph object.
    echo "fetching $bm"
    scp -O -r "$xfer:$bmdir/${bm}_[0-9]/endive/benchmarks/${bm}_ind-proof-tree-sd*" $local_dir &
    scp -O -r "$xfer:$bmdir/${bm}_[0-9]/endive/benchmarks/${bm}_IndDecompProof_*.tla" $local_dir &
done
wait

#
# Also fetch these other ones.
#

# Check for existence of "AsyncRaft" in bms.
if [[ $bms == *"AsyncRaft"* ]]; then
    for tag in "OnePrimaryPerTerm" "PrimaryHasEntriesItCreated" "OnePrimaryPerTerm_broken"
    do
        for seed in 1 2 3 4 5 6 7 8
        do
        scp -O -r "$xfer:$bmdir/AsyncRaft_${tag}_$seed/endive/benchmarks/AsyncRaft_ind-proof-tree-sd$seed.pdf" $local_dir/AsyncRaft_${tag}_ind-proof-tree-sd$seed.pdf &
        scp -O -r "$xfer:$bmdir/AsyncRaft_${tag}_$seed/endive/benchmarks/AsyncRaft_ind-proof-tree-sd$seed.proofgraph.json" $local_dir/AsyncRaft_${tag}_ind-proof-tree-sd$seed.proofgraph.json &
        # scp -O -r "neudiscovery:$bmdir/AsyncRaft_${tag}_$seed/endive/benchmarks/AsyncRaft_IndDecompProof_$seed.tla" $local_dir/AsyncRaft_${tag}_IndDecompProof_$seed.tla
        done
    done
    wait
fi

scp -O -r "$xfer:$bmdir/LamportMutex_broken_grammar/endive/benchmarks/LamportMutex_ind-proof-tree-sd3.pdf" $local_dir/LamportMutex_broken_grammar_ind-proof-tree-sd3.pdf
scp -O -r "$xfer:$bmdir/consensus_epr_broken_grammar/endive/benchmarks/consensus_epr_ind-proof-tree-sd3.pdf" $local_dir/consensus_epr_broken_grammar_ind-proof-tree-sd3.pdf
scp -O -r "$xfer:$bmdir/consensus_epr_broken_grammar_2/endive/benchmarks/consensus_epr_ind-proof-tree-sd3.pdf" $local_dir/consensus_epr_broken_grammar_2_ind-proof-tree-sd3.pdf

./discovery_job_status.sh