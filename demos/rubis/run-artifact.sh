#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.rubis.RubisBenchmark'
JAR_NAME='target/rubis-4.0.0-allinone.jar'

N_PROCS=$(seq 0 3)

# Executes a benchmark on N_PROCS hosts
function executeBench() {
  echo Run configuration "$1"
  # run processes and store pids in array
  for i in ${N_PROCS}; do
      java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "$1bench${i}.conf" &
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
executeBench 'local/weak_datacentric/'
executeBench 'local/strong_datacentric/'

# Collect results
python3 ../collect-results.py benchmark/measurements/rubis/bench-results benchmark/rubis

# Process the results
python3 ../process-results.py artifact-processed.csv \
 benchmark/rubis/weak/:100 \
 benchmark/rubis/op_mixed/:100 \
 benchmark/rubis/strong/:100 \
 benchmark/rubis/weak_datacentric/:100 \
 benchmark/rubis/mixed/:100 \
 benchmark/rubis/strong_datacentric/:100

# Generate and show the graphs
python3 ../generate-graphs.py latency_artifact-processed.csv artifact-normalized.csv \
 benchmark/rubis/weak/:benchmark/rubis/op_mixed/ \
 benchmark/rubis/strong/:benchmark/rubis/op_mixed/ \
 benchmark/rubis/weak_datacentric/:benchmark/rubis/op_mixed/ \
 benchmark/rubis/mixed/:benchmark/rubis/op_mixed/ \
 benchmark/rubis/strong_datacentric/:benchmark/rubis/op_mixed/
