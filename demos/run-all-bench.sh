#!/bin/bash

printf "~ COUNTER\n\n"
cd counter
./run-all-bench.sh

printf "~ MESSAGE-GROUPS\n\n"
cd ../message-groups
./run-all-bench.sh

printf "~ TWITTER-CLONE\n\n"
cd ../twitter-clone
./run-all-bench.sh

printf "~ RUBIS\n\n"
cd ../rubis
./run-all-bench.sh

printf "~ QUODDY\n\n"
cd ../quoddy
./run-all-bench.sh
