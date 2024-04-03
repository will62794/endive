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
    scp -O -r "neudiscovery:$bmdir/${bm}_[0-9]/endive/benchmarks/${bm}_ind-proof-tree-sd*" $local_dir
    scp -O -r "neudiscovery:$bmdir/${bm}_[0-9]/endive/benchmarks/${bm}_IndDecompProof_*.tla" $local_dir
    # TODO: Should be able to remove this second copy after proof grap renaming.
    # scp -O -r "neudiscovery:$bmdir/$bm/endive/benchmarks/${bm}*proofgraph*.json" $local_dir
done

#
# Also fetch these other ones.
#

for seed in 1 2 3 4 5 6
do
scp -O -r "neudiscovery:$bmdir/AsyncRaft_OnePrimaryPerTerm_$seed/endive/benchmarks/AsyncRaft_ind-proof-tree-sd$seed.pdf" $local_dir/AsyncRaft_OnePrimaryPerTerm_ind-proof-tree-sd$seed.pdf
scp -O -r "neudiscovery:$bmdir/AsyncRaft_LogMatching_$seed/endive/benchmarks/AsyncRaft_ind-proof-tree-sd$seed.pdf" $local_dir/AsyncRaft_LogMatching_ind-proof-tree-sd$seed.pdf
done

scp -O -r "neudiscovery:$bmdir/LamportMutex_broken_grammar/endive/benchmarks/LamportMutex_ind-proof-tree-sd3.pdf" $local_dir/LamportMutex_broken_grammar_ind-proof-tree-sd3.pdf
scp -O -r "neudiscovery:$bmdir/consensus_epr_broken_grammar/endive/benchmarks/consensus_epr_ind-proof-tree-sd3.pdf" $local_dir/consensus_epr_broken_grammar_ind-proof-tree-sd3.pdf
scp -O -r "neudiscovery:$bmdir/consensus_epr_broken_grammar_2/endive/benchmarks/consensus_epr_ind-proof-tree-sd3.pdf" $local_dir/consensus_epr_broken_grammar_2_ind-proof-tree-sd3.pdf

./discovery_job_status.sh