#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark'
JAR_NAME='target/message-groups-4.0.0-allinone.jar'

N_PROCS=$(seq 0 3)

replica-start.sh

# Executes a benchmark on N_PROCS hosts
function executeBench() {
  echo Run configuration "$1"
  # run processes and store pids in array
  for i in ${N_PROCS}; do
      java -cp "${JAR_NAME}" "${CLASS_NAME}"  -b cassandra -c "$1bench${i}.conf" &
      pids[${i}]=$!
  done
  # wait for all benchmarks to stop
  for pid in ${pids[*]}; do
      wait $pid
  done
  echo Finished configuration "$1"
}

# Run all processes with mixed configuration
executeBench 'local/weak/'
executeBench 'local/op_mixed/'
executeBench 'local/mixed/'
executeBench 'local/strong/'

# Collect results
python3 ../collect-results.py benchmark/measurements/message-groups/bench-results benchmark/message-groups

# Process the results
python3 ../process-results.py artifact-processed.csv \
 benchmark/message-groups/weak/:100 \
 benchmark/message-groups/op_mixed/:100 \
 benchmark/message-groups/mixed/:100 \
 benchmark/message-groups/strong/:100

# Generate and show the graphs
python3 ../generate-graphs.py latency_artifact-processed.csv artifact-normalized.csv \
 benchmark/message-groups/weak/:benchmark/message-groups/op_mixed/ \
 benchmark/message-groups/mixed/:benchmark/message-groups/op_mixed/ \
 benchmark/message-groups/strong/:benchmark/message-groups/op_mixed/
