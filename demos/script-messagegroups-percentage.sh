#!/bin/bash

python3 process-results.py processed-msggrps-percentage.csv \
results/strong-weak/local/messageGroups-00perc-weak/:1 \
results/strong-weak/local/messageGroups-25perc-weak/:1 \
results/strong-weak/local/messageGroups-50perc-weak/:1 \
results/strong-weak/local/messageGroups-75perc-weak/:1 \
results/strong-weak/local/messageGroups-100perc-weak/:1 \
results/strong-weak/datacenter/messageGroups-00perc-weak/:1 \
results/strong-weak/datacenter/messageGroups-25perc-weak/:1 \
results/strong-weak/datacenter/messageGroups-50perc-weak/:1 \
results/strong-weak/datacenter/messageGroups-75perc-weak/:1 \
results/strong-weak/datacenter/messageGroups-100perc-weak/:1 \
results/strong-weak/geodist/messageGroups-00perc-weak/:1 \
results/strong-weak/geodist/messageGroups-25perc-weak/:1 \
results/strong-weak/geodist/messageGroups-50perc-weak/:1 \
results/strong-weak/geodist/messageGroups-75perc-weak/:1 \
results/strong-weak/geodist/messageGroups-100perc-weak/:1


python3 generate-graphs.py processed-msggrps-percentage.csv normalized-msggrps-percentage.csv \
results/strong-weak/local/messageGroups-25perc-weak/:results/strong-weak/local/messageGroups-00perc-weak/ \
results/strong-weak/local/messageGroups-50perc-weak/:results/strong-weak/local/messageGroups-00perc-weak/ \
results/strong-weak/local/messageGroups-75perc-weak/:results/strong-weak/local/messageGroups-00perc-weak/ \
results/strong-weak/local/messageGroups-100perc-weak/:results/strong-weak/local/messageGroups-00perc-weak/ \
results/strong-weak/datacenter/messageGroups-25perc-weak/:results/strong-weak/datacenter/messageGroups-00perc-weak/ \
results/strong-weak/datacenter/messageGroups-50perc-weak/:results/strong-weak/datacenter/messageGroups-00perc-weak/ \
results/strong-weak/datacenter/messageGroups-75perc-weak/:results/strong-weak/datacenter/messageGroups-00perc-weak/ \
results/strong-weak/datacenter/messageGroups-100perc-weak/:results/strong-weak/datacenter/messageGroups-00perc-weak/ \
results/strong-weak/geodist/messageGroups-25perc-weak/:results/strong-weak/geodist/messageGroups-00perc-weak/ \
results/strong-weak/geodist/messageGroups-50perc-weak/:results/strong-weak/geodist/messageGroups-00perc-weak/ \
results/strong-weak/geodist/messageGroups-75perc-weak/:results/strong-weak/geodist/messageGroups-00perc-weak/ \
results/strong-weak/geodist/messageGroups-100perc-weak/:results/strong-weak/geodist/messageGroups-00perc-weak/
