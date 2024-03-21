#!/bin/sh
#
# Run batch script on Discovery cluster.
#

specname=$1
echo "Launching '$specname' script."
scriptname="discovery_${specname}_script.sh"

# Copy the batch script to the Discovery cluster.
echo "Copying script 'discovery_scripts/$scriptname' to Discovery cluster..."
scp -O discovery_scripts/$scriptname neudiscovery:/home/schultz.w

# Launch the script.
echo "Launching the script"
ssh neudiscovery "sbatch $scriptname"

# Now list the running jobs on Discovery cluster.
# ssh neudiscovery "squeue -u schultz.w"
./discovery_job_status.sh