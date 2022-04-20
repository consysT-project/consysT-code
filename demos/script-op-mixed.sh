#!/bin/bash

python3 process-results.py processed-op-mixed.csv \
../results/default/large-local-bench-results/counter/mixed/:100 \
../results/default/large-local-bench-results/counter/strong/:100 \
../results/default/large-local-bench-results/counter/weak/:100 \
../results/default/large-local-bench-results/message-groups/mixed/:100 \
../results/default/large-local-bench-results/message-groups/strong/:100 \
../results/default/large-local-bench-results/message-groups/weak/:100 \
../results/default/large-local-bench-results/quoddy/mixed/:100 \
../results/default/large-local-bench-results/quoddy/weak/:100 \
../results/default/large-local-bench-results/rubis/mixed/:100 \
../results/default/large-local-bench-results/rubis/strong/:100 \
../results/default/large-local-bench-results/rubis/weak/:100 \
../results/default/large-local-bench-results/twitter-clone/mixed/:100 \
../results/default/large-local-bench-results/twitter-clone/strong/:100 \
../results/default/large-local-bench-results/twitter-clone/weak/:100




python3 generate-graphs.py latency_processed-op-mixed.csv latency_normalized-op-mixed.csv \
../results/default/large-local-bench-results/counter/strong/:../results/default/large-local-bench-results/counter/mixed/ \
../results/default/large-local-bench-results/counter/weak/:../results/default/large-local-bench-results/counter/mixed/ \
../results/default/large-local-bench-results/message-groups/strong/:../results/default/large-local-bench-results/message-groups/mixed/ \
../results/default/large-local-bench-results/message-groups/weak/:../results/default/large-local-bench-results/message-groups/mixed/ \
../results/default/large-local-bench-results/quoddy/weak/:../results/default/large-local-bench-results/quoddy/mixed/ \
../results/default/large-local-bench-results/rubis/strong/:../results/default/large-local-bench-results/rubis/mixed/ \
../results/default/large-local-bench-results/rubis/weak/:../results/default/large-local-bench-results/rubis/mixed/ \
../results/default/large-local-bench-results/twitter-clone/strong/:../results/default/large-local-bench-results/twitter-clone/mixed/ \
../results/default/large-local-bench-results/twitter-clone/weak/:../results/default/large-local-bench-results/twitter-clone/mixed/


python3 generate-graphs.py throughput_processed-op-mixed.csv throughput_normalized-op-mixed.csv \
../results/default/large-local-bench-results/counter/strong/:../results/default/large-local-bench-results/counter/mixed/ \
../results/default/large-local-bench-results/counter/weak/:../results/default/large-local-bench-results/counter/mixed/ \
../results/default/large-local-bench-results/message-groups/strong/:../results/default/large-local-bench-results/message-groups/mixed/ \
../results/default/large-local-bench-results/message-groups/weak/:../results/default/large-local-bench-results/message-groups/mixed/ \
../results/default/large-local-bench-results/quoddy/weak/:../results/default/large-local-bench-results/quoddy/mixed/ \
../results/default/large-local-bench-results/rubis/strong/:../results/default/large-local-bench-results/rubis/mixed/ \
../results/default/large-local-bench-results/rubis/weak/:../results/default/large-local-bench-results/rubis/mixed/ \
../results/default/large-local-bench-results/twitter-clone/strong/:../results/default/large-local-bench-results/twitter-clone/mixed/ \
../results/default/large-local-bench-results/twitter-clone/weak/:../results/default/large-local-bench-results/twitter-clone/mixed/