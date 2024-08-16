#!/bin/bash

python3 ../../../process-results.py processed.csv \
../2024-02-09_aws-benchs/invariants-bank-account/mixed/:1000 \
../2024-02-09_aws-benchs/invariants-bank-account/strong/:1000 \
../2024-02-09_aws-benchs/invariants-bank-account-lww/mixed/:1000 \
../2024-02-09_aws-benchs/invariants-bank-account-lww/strong/:1000 \
../2024-02-09_aws-benchs/invariants-consensus/mixed/:1000 \
../2024-02-09_aws-benchs/invariants-consensus/strong/:1000 \
../2024-02-09_aws-benchs/invariants-credit-account/mixed/:1000 \
../2024-02-09_aws-benchs/invariants-credit-account/strong/:1000 \
../2024-02-09_aws-benchs/invariants-distributed-lock/mixed/:1000 \
../2024-02-09_aws-benchs/invariants-distributed-lock/strong/:1000 \
../2024-02-09_aws-benchs/invariants-joint-bank-account/mixed/:1000 \
../2024-02-09_aws-benchs/invariants-joint-bank-account/strong/:1000 \
./invariants-message-groups/mixed/:1000 \
./invariants-message-groups/strong/:1000 \
../2024-02-09_aws-benchs/invariants-resettable-counter/mixed/:1000 \
../2024-02-09_aws-benchs/invariants-resettable-counter/strong/:1000 \
./invariants-tournaments/mixed/:1000 \
./invariants-tournaments/strong/:1000



python3 ../../../generate-graphs.py latency_processed.csv latency_normalized.csv \
../2024-02-09_aws-benchs/invariants-bank-account/mixed/:../2024-02-09_aws-benchs/invariants-bank-account/strong/ \
../2024-02-09_aws-benchs/invariants-bank-account-lww/mixed/:../2024-02-09_aws-benchs/invariants-bank-account-lww/strong/ \
../2024-02-09_aws-benchs/invariants-consensus/mixed/:../2024-02-09_aws-benchs/invariants-consensus/strong/ \
../2024-02-09_aws-benchs/invariants-credit-account/mixed/:../2024-02-09_aws-benchs/invariants-credit-account/strong/ \
../2024-02-09_aws-benchs/invariants-distributed-lock/mixed/:../2024-02-09_aws-benchs/invariants-distributed-lock/strong/ \
../2024-02-09_aws-benchs/invariants-joint-bank-account/mixed/:../2024-02-09_aws-benchs/invariants-joint-bank-account/strong/ \
./invariants-message-groups/mixed/:./invariants-message-groups/strong/ \
../2024-02-09_aws-benchs/invariants-resettable-counter/mixed/:../2024-02-09_aws-benchs/invariants-resettable-counter/strong/ \
./invariants-tournaments/mixed/:./invariants-tournaments/strong/



python3 ../../../generate-graphs.py throughput_processed.csv throughput_normalized.csv \
../2024-02-09_aws-benchs/invariants-bank-account/mixed/:../2024-02-09_aws-benchs/invariants-bank-account/strong/ \
../2024-02-09_aws-benchs/invariants-bank-account-lww/mixed/:../2024-02-09_aws-benchs/invariants-bank-account-lww/strong/ \
../2024-02-09_aws-benchs/invariants-consensus/mixed/:../2024-02-09_aws-benchs/invariants-consensus/strong/ \
../2024-02-09_aws-benchs/invariants-credit-account/mixed/:../2024-02-09_aws-benchs/invariants-credit-account/strong/ \
../2024-02-09_aws-benchs/invariants-distributed-lock/mixed/:../2024-02-09_aws-benchs/invariants-distributed-lock/strong/ \
../2024-02-09_aws-benchs/invariants-joint-bank-account/mixed/:../2024-02-09_aws-benchs/invariants-joint-bank-account/strong/ \
./invariants-message-groups/mixed/:./invariants-message-groups/strong/ \
../2024-02-09_aws-benchs/invariants-resettable-counter/mixed/:../2024-02-09_aws-benchs/invariants-resettable-counter/strong/ \
./invariants-tournaments/mixed/:./invariants-tournaments/strong/
