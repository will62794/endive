#!/bin/sh
#
# Run benchmark batch script on Discovery cluster.
#
# Can run with ./discovery_launch.sh <specname1> <specname2> ...
#

args=$@

# Copy all scripts.
echo "Copying scripts in 'discovery_scripts' to Discovery cluster..."
scp -O discovery_scripts/*.sh neudiscovery:/home/schultz.w
scp -O discovery_scripts/*.script neudiscovery:/home/schultz.w

for specname in $args
do
    echo "Launching '$specname' script."
    scriptname="discovery_${specname}.script"

    # Launch the script.
    echo "Launching the script"
    jobname="${specname}_endive_Job"
    outfile="/scratch/schultz.w/endive_logs/${specname}_job_output.txt"
    ssh neudiscovery "sbatch -J $jobname -o $outfile $scriptname"
done

# Now list the running jobs on Discovery cluster.
# ssh neudiscovery "squeue -u schultz.w"
./discovery_job_status.sh