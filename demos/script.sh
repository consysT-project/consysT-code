#!/bin/bash

python3 process-results.py processed.csv results/counter-mixed/:100 results/counter-strong/:100 results/concertTickets-mixed/:100 results/concertTickets-strong/:100 results/eshop-mixed/:100 results/eshop-strong/:10  results/messageGroups-mixed/:100 results/messageGroups-strong/:100  results/twitterClone-mixed/:100 results/twitterClone-strong/:100

python3 generate-graphs.py processed.csv normalized.csv results/counter-mixed/:results/counter-strong/ results/concertTickets-mixed/:results/concertTickets-strong/ results/messageGroups-mixed/:results/messageGroups-strong/ results/eshop-mixed/:results/eshop-strong/ results/twitterClone-mixed/:results/twitterClone-strong/
