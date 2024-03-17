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

# Now list the running jobs on Discovery cluster.
ssh neudiscovery "squeue -u schultz.w"