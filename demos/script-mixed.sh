#!/bin/bash

python3 process-results.py processed-mixed.csv \
results/case-studies/geodist/counter-mixed/:100 results/case-studies/geodist/counter-eventual/:100 results/case-studies/geodist/counter-strong/:100 \
results/case-studies/geodist/concertTickets-mixed/:100 results/case-studies/geodist/concertTickets-strong/:100 \
results/case-studies/geodist/eshop-mixed/:100 results/case-studies/geodist/eshop-strong/:10 results/case-studies/geodist/eshop-strong-with-10mswait/:1 \
results/case-studies/geodist/messageGroups-mixed/:100 results/case-studies/geodist/messageGroups-causal/:100 results/case-studies/geodist/messageGroups-strong/:100 \
results/case-studies/geodist/twitterClone-mixed/:100 results/case-studies/geodist/twitterClone-mixed-lesssync/:100 results/case-studies/geodist/twitterClone-strong/:100 \
results/case-studies/local/counter-mixed/:100 results/case-studies/local/counter-strong/:100 \
results/case-studies/local/concert-mixed/:100 results/case-studies/local/concert-strong/:100 \
results/case-studies/local/eshop-mixed/:10 results/case-studies/local/eshop-strong/:10 \
results/case-studies/local/messageGroups-eventual/:100 results/case-studies/local/messageGroups-strong/:100 \
results/case-studies/local/twitterClone-mixed/:100 results/case-studies/local/twitterClone-strong/:100 \
results/case-studies/datacenter/counter-mixed/:100 results/case-studies/datacenter/counter-strong/:100 \
results/case-studies/datacenter/concert-mixed/:100 results/case-studies/datacenter/concert-strong/:100 \
results/case-studies/datacenter/eshop-mixed/:10 results/case-studies/datacenter/eshop-strong/:10 results/case-studies/datacenter/eshop-strong-with-10mswait/:1 \
results/case-studies/datacenter/messageGroups-eventual/:100 results/case-studies/datacenter/messageGroups-strong/:100 \
results/case-studies/datacenter/twitterClone-mixed/:100 results/case-studies/datacenter/twitterClone-strong/:100 

python3 generate-graphs.py processed-mixed.csv normalized-mixed.csv results/case-studies/geodist/counter-eventual/:results/case-studies/geodist/counter-strong/ results/case-studies/geodist/concertTickets-mixed/:results/case-studies/geodist/concertTickets-strong/ results/case-studies/geodist/messageGroups-mixed/:results/case-studies/geodist/messageGroups-strong/ results/case-studies/geodist/eshop-mixed/:results/case-studies/geodist/eshop-strong/ results/case-studies/geodist/twitterClone-mixed-lesssync/:results/case-studies/geodist/twitterClone-strong/ results/case-studies/local/counter-mixed/:results/case-studies/local/counter-strong/ results/case-studies/local/concert-mixed/:results/case-studies/local/concert-strong/ results/case-studies/local/eshop-mixed/:results/case-studies/local/eshop-strong/ results/case-studies/local/messageGroups-eventual/:results/case-studies/local/messageGroups-strong/ results/case-studies/local/twitterClone-mixed/:results/case-studies/local/twitterClone-strong/ results/case-studies/datacenter/counter-mixed/:results/case-studies/datacenter/counter-strong/ results/case-studies/datacenter/concert-mixed/:results/case-studies/datacenter/concert-strong/ results/case-studies/datacenter/eshop-mixed/:results/case-studies/datacenter/eshop-strong/ results/case-studies/datacenter/messageGroups-eventual/:results/case-studies/datacenter/messageGroups-strong/ results/case-studies/datacenter/twitterClone-mixed/:results/case-studies/datacenter/twitterClone-strong/
