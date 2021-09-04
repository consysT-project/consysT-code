#!/bin/bash

python3 process-results.py processed-invariant.csv \
results/invariants/bankaccount/opmixed/:1000 results/invariants/bankaccount/opstrong/:1000 \
results/invariants/bankaccountlww/opmixed/:1000 results/invariants/bankaccountlww/opstrong/:1000 \
results/invariants/consensus/opmixed/:1000 results/invariants/consensus/opstrong/:1000 \
results/invariants/creditaccount/opmixed/:1000 results/invariants/creditaccount/opstrong/:1000 \
results/invariants/distributedlock/opmixed/:1000 results/invariants/distributedlock/opstrong/:1000 \
results/invariants/jointbankaccount/opmixed/:1000 results/invariants/jointbankaccount/opstrong/:1000 \
results/invariants/resettablecounter/opmixed/:1000 results/invariants/resettablecounter/opstrong/:1000 \
results/invariants/tournament/opmixed/:1000 results/invariants/tournament/opstrong/:1000

python3 generate-graphs.py latency_processed-invariant.csv latency_normalized-invariant.csv \
results/invariants/bankaccount/opmixed/:results/invariants/bankaccount/opstrong/ \
results/invariants/bankaccountlww/opmixed/:results/invariants/bankaccountlww/opstrong/ \
results/invariants/consensus/opmixed/:results/invariants/consensus/opstrong/ \
results/invariants/creditaccount/opmixed/:results/invariants/creditaccount/opstrong/ \
results/invariants/distributedlock/opmixed/:results/invariants/distributedlock/opstrong/ \
results/invariants/jointbankaccount/opmixed/:results/invariants/jointbankaccount/opstrong/ \
results/invariants/resettablecounter/opmixed/:results/invariants/resettablecounter/opstrong/ \
results/invariants/tournament/opmixed/:results/invariants/tournament/opstrong/

python3 generate-graphs.py throughput_processed-invariant.csv throughput_normalized-invariant.csv \
results/invariants/bankaccount/opmixed/:results/invariants/bankaccount/opstrong/ \
results/invariants/bankaccountlww/opmixed/:results/invariants/bankaccountlww/opstrong/ \
results/invariants/consensus/opmixed/:results/invariants/consensus/opstrong/ \
results/invariants/creditaccount/opmixed/:results/invariants/creditaccount/opstrong/ \
results/invariants/distributedlock/opmixed/:results/invariants/distributedlock/opstrong/ \
results/invariants/jointbankaccount/opmixed/:results/invariants/jointbankaccount/opstrong/ \
results/invariants/resettablecounter/opmixed/:results/invariants/resettablecounter/opstrong/ \
results/invariants/tournament/opmixed/:results/invariants/tournament/opstrong/