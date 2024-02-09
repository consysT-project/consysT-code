#!/bin/bash

python3 ../../../process-results.py processed.csv \
./invariants-bank-account/mixed/:1000 \
./invariants-bank-account/strong/:1000 \
./invariants-bank-account-lww/mixed/:1000 \
./invariants-bank-account-lww/strong/:1000 \
./invariants-consensus/mixed/:1000 \
./invariants-consensus/strong/:1000 \
./invariants-credit-account/mixed/:1000 \
./invariants-credit-account/strong/:1000 \
./invariants-distributed-lock/mixed/:1000 \
./invariants-distributed-lock/strong/:1000 \
./invariants-joint-bank-account/mixed/:1000 \
./invariants-joint-bank-account/strong/:1000 \
./invariants-resettable-counter/mixed/:1000 \
./invariants-resettable-counter/strong/:1000 \
./invariants-tournaments/mixed/:1000 \
./invariants-tournaments/strong/:1000



python3 ../../../generate-graphs.py latency_processed.csv latency_normalized.csv \
./invariants-bank-account/mixed/:./invariants-bank-account/strong/ \
./invariants-bank-account-lww/mixed/:./invariants-bank-account-lww/strong/ \
./invariants-consensus/mixed/:./invariants-consensus/strong/ \
./invariants-credit-account/mixed/:./invariants-credit-account/strong/ \
./invariants-distributed-lock/mixed/:./invariants-distributed-lock/strong/ \
./invariants-joint-bank-account/mixed/:./invariants-joint-bank-account/strong/ \
./invariants-resettable-counter/mixed/:./invariants-resettable-counter/strong/ \
./invariants-tournaments/mixed/:./invariants-tournaments/strong/



python3 ../../../generate-graphs.py throughput_processed.csv throughput_normalized.csv \
./invariants-bank-account/mixed/:./invariants-bank-account/strong/ \
./invariants-bank-account-lww/mixed/:./invariants-bank-account-lww/strong/ \
./invariants-consensus/mixed/:./invariants-consensus/strong/ \
./invariants-credit-account/mixed/:./invariants-credit-account/strong/ \
./invariants-distributed-lock/mixed/:./invariants-distributed-lock/strong/ \
./invariants-joint-bank-account/mixed/:./invariants-joint-bank-account/strong/ \
./invariants-resettable-counter/mixed/:./invariants-resettable-counter/strong/ \
./invariants-tournaments/mixed/:./invariants-tournaments/strong/
