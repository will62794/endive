#!/bin/sh
#
# Download logs and other data from Discovery server.
#
mkdir -p discovery_data

scp -O -r neudiscovery:/scratch/schultz.w/endive_logs discovery_data

# Also fetch Hermes,AsyncRaft proof stuff.
scp -O -r "neudiscovery:/scratch/schultz.w/benchmarking/Hermes/endive/benchmarks/Hermes_ind-proof-tree-sd*.pdf" discovery_data
scp -O -r "neudiscovery:/scratch/schultz.w/benchmarking/AsyncRaft/endive/benchmarks/AsyncRaft_ind-proof-tree-sd*.pdf" discovery_data
scp -O -r "neudiscovery:/scratch/schultz.w/benchmarking/AsyncRaft_OnePrimaryPerTerm_2/endive/benchmarks/AsyncRaft_ind-proof-tree-sd2.pdf" discovery_data/AsyncRaft_OnePrimaryPerTerm_ind-proof-tree-sd2.pdf
scp -O -r "neudiscovery:/scratch/schultz.w/benchmarking/Boulanger/endive/benchmarks/Boulanger_ind-proof-tree-sd*.pdf" discovery_data
scp -O -r "neudiscovery:/scratch/schultz.w/benchmarking/Bakery/endive/benchmarks/Bakery_ind-proof-tree-sd*.pdf" discovery_data
scp -O -r "neudiscovery:/scratch/schultz.w/benchmarking/consensus_epr/endive/benchmarks/consensus_epr_ind-proof-tree-sd*.pdf" discovery_data
scp -O -r "neudiscovery:/scratch/schultz.w/benchmarking/ZeusReliableCommit/endive/benchmarks/ZeusReliableCommit_ind-proof-tree-sd*.pdf" discovery_data

scp -O -r "neudiscovery:/scratch/schultz.w/benchmarking/Boulanger/endive/benchmarks/Boulanger*proofgraph.json" discovery_data

./discovery_job_status.sh