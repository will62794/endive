#!/bin/sh
#
# Run Hermes batch script on Discovery cluster.
#

scriptname="discovery_run_Hermes.sh"

# Copy the batch script to the Discovery cluster.
echo "Copying script $scriptname to Discovery cluster..."
scp -O discovery_run_Hermes.sh neudiscovery:/home/schultz.w

# Launch the script.
echo "Launching the script"
ssh neudiscovery "sbatch discovery_run_Hermes.sh"

# List all my running jobs on Discovery cluster.
ssh neudiscovery "squeue -u schultz.w"

# Cancel a job on Discovery cluster.
# ssh neudiscovery "scancel <JOBID>"
