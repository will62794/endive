#!/bin/sh

# Show detailed info on all jobs for my username.
# ssh neudiscovery 'squeue -u schultz.w'
ssh neudiscovery 'squeue -o "%.18i %.9P %.35j %.8u %.2t %.10M %.6D %.18R %.8C" -u schultz.w'

# If "detailed" argument is passed then run the below command:
if [ "$1" = "detailed" ]; then
    ssh neudiscovery 'squeue -u schultz.w --format "%i" --noheader | xargs scontrol show jobid -dd'
fi

# Cancel all my jobs.
if [ "$1" = "cancel_all" ]; then
    ssh neudiscovery 'squeue -u schultz.w --format "%i" --noheader | xargs scancel'
fi

