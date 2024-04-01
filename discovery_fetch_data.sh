#!/bin/sh
#
# Download logs and other data from Discovery server.
#
mkdir -p discovery_data

scp -O -r neudiscovery:/scratch/schultz.w/endive_logs discovery_data

bmdir="/scratch/schultz.w/benchmarking"
local_dir="discovery_data/proof_trees"
mkdir -p $local_dir

# Also fetch Hermes,AsyncRaft proof stuff.
scp -O -r "neudiscovery:$bmdir/Hermes/endive/benchmarks/Hermes_ind-proof-tree-sd*.pdf" $local_dir
scp -O -r "neudiscovery:$bmdir/AsyncRaft/endive/benchmarks/AsyncRaft_ind-proof-tree-sd*.pdf" $local_dir
scp -O -r "neudiscovery:$bmdir/AsyncRaft_OnePrimaryPerTerm_2/endive/benchmarks/AsyncRaft_ind-proof-tree-sd2.pdf" $local_dir/AsyncRaft_OnePrimaryPerTerm_ind-proof-tree-sd2.pdf
scp -O -r "neudiscovery:$bmdir/Boulanger/endive/benchmarks/Boulanger_ind-proof-tree-sd*.pdf" $local_dir
scp -O -r "neudiscovery:$bmdir/Bakery/endive/benchmarks/Bakery_ind-proof-tree-sd*.pdf" $local_dir
scp -O -r "neudiscovery:$bmdir/consensus_epr/endive/benchmarks/consensus_epr_ind-proof-tree-sd*.pdf" $local_dir
scp -O -r "neudiscovery:$bmdir/LamportMutex/endive/benchmarks/LamportMutex_ind-proof-tree-sd*.pdf" $local_dir
scp -O -r "neudiscovery:$bmdir/TwoPhase/endive/benchmarks/TwoPhase_ind-proof-tree-sd*.pdf" $local_dir
scp -O -r "neudiscovery:$bmdir/ZeusReliableCommit/endive/benchmarks/ZeusReliableCommit_ind-proof-tree-sd*.pdf" $local_dir

scp -O -r "neudiscovery:$bmdir/Boulanger/endive/benchmarks/Boulanger*proofgraph.json" $local_dir

# Also fetch data to paper directory for stats used there.


./discovery_job_status.sh