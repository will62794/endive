#!/bin/sh
#
# Download logs and other data from Discovery server.
#
mkdir -p discovery_data

scp -O -r neudiscovery:/home/schultz.w/endive_logs discovery_data

# Also fetch Hermes,AsyncRaft proof stuff.
scp -O -r neudiscovery:/home/schultz.w/endive/benchmarks/Hermes_ind-proof-tree.pdf discovery_data
scp -O -r neudiscovery:/home/schultz.w/benchmarking/AsyncRaft/endive/benchmarks/AsyncRaft_ind-proof-tree.pdf discovery_data
scp -O -r neudiscovery:/home/schultz.w/benchmarking/Boulanger/endive/benchmarks/Boulanger_ind-proof-tree.pdf discovery_data
