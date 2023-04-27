#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.counter.CounterBenchmark'
JAR_NAME='target/counter-4.0.0-allinone.jar'

N_PROCS=`seq 0 4`

replica-start.sh

# Executes a benchmark on N_PROCS hosts
function executeBench() {
  echo Run configuration $1
  # run processes and store pids in array
  for i in ${N_PROCS}; do
      java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "$1bench${i}.conf" &
      pids[${i}]=$!
  done
  # wait for all benchmarks to stop
  for pid in ${pids[*]}; do
      wait $pid
  done
  echo Finished configuration $1
}

# Run all processes with mixed configuration
executeBench 'local/weak/'
executeBench 'local/op_mixed/'
executeBench 'local/mixed/'
executeBench 'local/strong/'

# Process the results
python3 ../process-results.py artifact-processed.csv \
 bench-results/weak/:100 \
 bench-results/mixed/:100 \
 bench-results/strong/:100

# Generate and show the graphs
python3 ../generate-graphs.py artifact-processed.csv artifact-normalized.csv \
 bench-results/weak/:bench-results/strong/ \
 bench-results/mixed/:bench-results/strong/
