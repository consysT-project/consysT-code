#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.eshop.EShopBenchmark'
JAR_NAME='target/eshop-2.0.0-allinone.jar'

N_PROCS=`seq 0 8`

# Executes a benchmark on N_PROCS hosts
function executeBench() {
  echo Run configuration $1 with $2
  # run processes and store pids in array
  for i in ${N_PROCS}; do
      java -cp "${JAR_NAME}" "${CLASS_NAME}" "$1bench${i}.conf" "$2" &
      pids[${i}]=$!
  done
  # wait for all benchmarks to stop
  for pid in ${pids[*]}; do
      wait $pid
  done
  echo Finished configuration $1
}

# Run all processes with mixed configuration
executeBench 'local/weak/' './bench-results/artifact/weak'
executeBench 'local/mixed/' './bench-results/artifact/mixed'
executeBench 'local/strong/' './bench-results/artifact/strong'

# Process the results
python3 ../process-results.py artifact-processed.csv \
 bench-results/artifact/weak/:1 \
 bench-results/artifact/mixed/:1 \
 bench-results/artifact/strong/:1

# Generate and show the graphs
python3 ../generate-graphs.py artifact-processed.csv artifact-normalized.csv \
 bench-results/artifact/weak/:bench-results/artifact/strong/ \
 bench-results/artifact/mixed/:bench-results/artifact/strong/
