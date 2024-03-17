#!/bin/sh
# Download logs and other data from Discovery server.
mkdir -p discovery_data
scp -O -r neudiscovery:/home/schultz.w/endive_logs discovery_data
