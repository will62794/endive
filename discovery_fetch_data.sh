#!/bin/sh
#
# Download logs and other data from Discovery server.
#
mkdir -p discovery_data

echo "Fetching logs"
scp -O -r neudiscovery:/scratch/schultz.w/endive_logs discovery_data

bmdir="/scratch/schultz.w/benchmarking"
local_dir="discovery_data/proof_graphs"
mkdir -p $local_dir

# Fetch proof graph stuff.
bms="TwoPhase consensus_epr LamportMutex Hermes ZeusReliableCommit Boulanger Bakery AsyncRaft"
echo "Fetching proof graphs."
for bm in $bms
do
    # Fetch rendered proof tree and proof graph object.
    scp -O -r "neudiscovery:$bmdir/$bm/endive/benchmarks/${bm}_ind-proof-tree-sd*" $local_dir
    # TODO: Should be able to remove this second copy after proof grap renaming.
    scp -O -r "neudiscovery:$bmdir/$bm/endive/benchmarks/${bm}*proofgraph*.json" $local_dir
done

# Also fetch this other one.
scp -O -r "neudiscovery:$bmdir/AsyncRaft_OnePrimaryPerTerm_2/endive/benchmarks/AsyncRaft_ind-proof-tree-sd2.pdf" $local_dir/AsyncRaft_OnePrimaryPerTerm_ind-proof-tree-sd2.pdf

./discovery_job_status.sh