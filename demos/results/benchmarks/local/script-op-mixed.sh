#!/bin/bash

python3 ../../process-results.py processed.csv \
./counter/op_mixed/:100 \
./counter/mixed/:100 \
./counter/strong/:100 \
./counter/weak/:100 \
./message-groups/op_mixed/:100 \
./message-groups/mixed/:100 \
./message-groups/strong/:100 \
./message-groups/weak/:100 \
./twitter-clone/op_mixed/:100 \
./twitter-clone/mixed/:100 \
./twitter-clone/strong/:100 \
./twitter-clone/weak/:100 \
./quoddy/op_mixed/:100 \
./quoddy/mixed/:100 \
./quoddy/strong/:100 \
./quoddy/weak/:100 \
./rubis/op_mixed/:100 \
./rubis/mixed/:100 \
./rubis/strong/:100 \
./rubis/weak/:100


python3 ../../generate-graphs.py latency_processed.csv latency_normalized.csv \
./counter/strong/:./counter/op_mixed/ \
./counter/weak/:./counter/op_mixed/ \
./counter/mixed/:./counter/op_mixed/ \
./message-groups/strong/:./message-groups/op_mixed/ \
./message-groups/weak/:./message-groups/op_mixed/ \
./message-groups/mixed/:./message-groups/op_mixed/ \
./twitter-clone/strong/:./twitter-clone/op_mixed/ \
./twitter-clone/weak/:./twitter-clone/op_mixed/ \
./twitter-clone/mixed/:./twitter-clone/op_mixed/ \
./quoddy/strong/:./quoddy/op_mixed/ \
./quoddy/weak/:./quoddy/op_mixed/ \
./quoddy/mixed/:./quoddy/op_mixed/ \
./rubis/strong/:./rubis/op_mixed/ \
./rubis/weak/:./rubis/op_mixed/ \
./rubis/mixed/:./rubis/op_mixed/

python3 ../../generate-graphs.py throughput_processed.csv throughput_normalized.csv \
./counter/strong/:./counter/op_mixed/ \
./counter/weak/:./counter/op_mixed/ \
./counter/mixed/:./counter/op_mixed/ \
./message-groups/strong/:./message-groups/op_mixed/ \
./message-groups/weak/:./message-groups/op_mixed/ \
./message-groups/mixed/:./message-groups/op_mixed/ \
./twitter-clone/strong/:./twitter-clone/op_mixed/ \
./twitter-clone/weak/:./twitter-clone/op_mixed/ \
./twitter-clone/mixed/:./twitter-clone/op_mixed/ \
./quoddy/strong/:./quoddy/op_mixed/ \
./quoddy/weak/:./quoddy/op_mixed/ \
./quoddy/mixed/:./quoddy/op_mixed/ \
./rubis/strong/:./rubis/op_mixed/ \
./rubis/weak/:./rubis/op_mixed/ \
./rubis/mixed/:./rubis/op_mixed/
