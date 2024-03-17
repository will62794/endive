#!/bin/sh

# Show detailed info on all jobs for my username.
ssh neudiscovery 'squeue -u schultz.w --format "%i" --noheader | xargs scontrol show jobid -dd'