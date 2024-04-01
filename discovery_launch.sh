#!/bin/sh
#
# Run benchmark batch script on Discovery cluster.
#
# Can run with ./discovery_launch.sh <specname1> <specname2> ...
#

args=$@

# Copy setup scripts.
echo "Copying scripts in 'discovery_scripts' to Discovery cluster..."
scp -O discovery_scripts/bm_setup.sh neudiscovery:/home/schultz.w

for specname in $args
do
    scriptname="discovery_${specname}.script"
    echo "Copying '$specname' script."
    scp -O discovery_scripts/$scriptname neudiscovery:/home/schultz.w

    # Launch the script.
    echo "Launching '$specname' script."
    jobname="${specname}_endive_Job"
    outfile="/scratch/schultz.w/endive_logs/${specname}_job_output.txt"
    ssh neudiscovery "sbatch -J $jobname -o $outfile $scriptname"
done

# Now list the running jobs on Discovery cluster.
# ssh neudiscovery "squeue -u schultz.w"
./discovery_job_status.sh