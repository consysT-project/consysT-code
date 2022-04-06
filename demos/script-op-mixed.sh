#!/bin/bash

python3 process-results.py processed-op-mixed.csv \
../results/default/local-bench-results/mixed/counter/:100 ../results/default/local-bench-results/strong/counter/:100 \
../results/default/local-bench-results/mixed/message-groups/:100 ../results/default/local-bench-results/strong/message-groups/:100


python3 generate-graphs.py latency_processed-op-mixed.csv latency_normalized-op-mixed.csv \
../results/default/local-bench-results/mixed/counter/:../results/default/local-bench-results/strong/counter/ \
../results/default/local-bench-results/mixed/message-groups/:../results/default/local-bench-results/strong/message-groups/


python3 generate-graphs.py throughput_processed-op-mixed.csv throughput_normalized-op-mixed.csv \
../results/default/local-bench-results/mixed/counter/:../results/default/local-bench-results/strong/counter/ \
../results/default/local-bench-results/mixed/message-groups/:../results/default/local-bench-results/strong/message-groups/