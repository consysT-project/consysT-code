#!/bin/bash

python3 ../../../process-results.py processed.csv \
./counter/weak/:1000 \
./counter/op_mixed/:1000 \
./counter/mixed/:1000 \
./counter/strong/:1000 \
./message-groups/weak/:1000 \
./message-groups/op_mixed/:1000 \
./message-groups/mixed/:1000 \
./message-groups/strong/:1000 \
./twitter-clone/weak/:1000 \
./twitter-clone/op_mixed/:1000 \
./twitter-clone/strong/:1000 \
./twitter-clone/weak_datacentric/:1000 \
./twitter-clone/mixed/:1000 \
./twitter-clone/strong_datacentric/:1000 \
./quoddy/weak/:1000 \
./quoddy/op_mixed/:1000 \
./quoddy/strong/:1000 \
./quoddy/weak_datacentric/:1000 \
./quoddy/mixed/:1000 \
./quoddy/strong_datacentric/:1000 \
./rubis/weak/:1000 \
./rubis/op_mixed/:1000 \
./rubis/strong/:1000 \
./rubis/weak_datacentric/:1000 \
./rubis/mixed/:1000 \
./rubis/strong_datacentric/:1000


python3 ../../../generate-graphs.py latency_processed.csv latency_normalized.csv \
./counter/strong/:./counter/op_mixed/ \
./counter/weak/:./counter/op_mixed/ \
./counter/mixed/:./counter/op_mixed/ \
./message-groups/strong/:./message-groups/op_mixed/ \
./message-groups/weak/:./message-groups/op_mixed/ \
./message-groups/mixed/:./message-groups/op_mixed/ \
./twitter-clone/strong/:./twitter-clone/op_mixed/ \
./twitter-clone/weak/:./twitter-clone/op_mixed/ \
./twitter-clone/mixed/:./twitter-clone/op_mixed/ \
./twitter-clone/weak_datacentric/:./twitter-clone/op_mixed/ \
./twitter-clone/strong_datacentric/:./twitter-clone/op_mixed/ \
./quoddy/strong/:./quoddy/op_mixed/ \
./quoddy/weak/:./quoddy/op_mixed/ \
./quoddy/mixed/:./quoddy/op_mixed/ \
./quoddy/weak_datacentric/:./quoddy/op_mixed/ \
./quoddy/strong_datacentric/:./quoddy/op_mixed/ \
./rubis/strong/:./rubis/op_mixed/ \
./rubis/weak/:./rubis/op_mixed/ \
./rubis/mixed/:./rubis/op_mixed/ \
./rubis/weak_datacentric/:./rubis/op_mixed/ \
./rubis/strong_datacentric/:./rubis/op_mixed/


python3 ../../../generate-graphs.py throughput_processed.csv throughput_normalized.csv \
./counter/strong/:./counter/op_mixed/ \
./counter/weak/:./counter/op_mixed/ \
./counter/mixed/:./counter/op_mixed/ \
./message-groups/strong/:./message-groups/op_mixed/ \
./message-groups/weak/:./message-groups/op_mixed/ \
./message-groups/mixed/:./message-groups/op_mixed/ \
./twitter-clone/strong/:./twitter-clone/op_mixed/ \
./twitter-clone/weak/:./twitter-clone/op_mixed/ \
./twitter-clone/mixed/:./twitter-clone/op_mixed/ \
./twitter-clone/weak_datacentric/:./twitter-clone/op_mixed/ \
./twitter-clone/strong_datacentric/:./twitter-clone/op_mixed/ \
./quoddy/strong/:./quoddy/op_mixed/ \
./quoddy/weak/:./quoddy/op_mixed/ \
./quoddy/mixed/:./quoddy/op_mixed/ \
./quoddy/weak_datacentric/:./quoddy/op_mixed/ \
./quoddy/strong_datacentric/:./quoddy/op_mixed/ \
./rubis/strong/:./rubis/op_mixed/ \
./rubis/weak/:./rubis/op_mixed/ \
./rubis/mixed/:./rubis/op_mixed/ \
./rubis/weak_datacentric/:./rubis/op_mixed/ \
./rubis/strong_datacentric/:./rubis/op_mixed/
