#!/bin/sh
#
# Run Hermes batch script on Discovery cluster.
#

scriptname="discovery_Hermes_script.sh"

# Copy the batch script to the Discovery cluster.
echo "Copying script $scriptname to Discovery cluster..."
scp -O $scriptname neudiscovery:/home/schultz.w

# Launch the script.
echo "Launching the script"
ssh neudiscovery "sbatch $scriptname"

# List all my running jobs on Discovery cluster.
ssh neudiscovery "squeue -u schultz.w"

# Cancel a job on Discovery cluster.
# ssh neudiscovery "scancel <JOBID>"
