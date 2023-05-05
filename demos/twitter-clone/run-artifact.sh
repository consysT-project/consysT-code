#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark'
JAR_NAME='target/twitter-clone-4.0.0-allinone.jar'

N_PROCS=`seq 0 3`

# Executes a benchmark on N_PROCS hosts
function executeBench() {
  echo Run configuration $1 with $2
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
executeBench 'local/weak_datacentric/'
executeBench 'local/strong_datacentric/'
executeBench 'local/datacentric_mixed_in_opcentric_impl/'

# Collect results
python3 ../collect-results.py benchmark/measurements/twitter-clone/bench-results benchmark/twitter-clone

# Process the results
python3 ../process-results.py artifact-processed.csv \
 benchmark/twitter-clone/weak/:100 \
 benchmark/twitter-clone/op_mixed/:100 \
 benchmark/twitter-clone/strong/:100 \
 benchmark/twitter-clone/weak_datacentric/:100 \
 benchmark/twitter-clone/mixed/:100 \
 benchmark/twitter-clone/strong_datacentric/:100 \
 benchmark/twitter-clone/datacentric_mixed_in_opcentric_impl/:100

# Generate and show the graphs
python3 ../generate-graphs.py latency_artifact-processed.csv artifact-normalized.csv \
 benchmark/twitter-clone/weak/:benchmark/twitter-clone/op_mixed/ \
 benchmark/twitter-clone/strong/:benchmark/twitter-clone/op_mixed/ \
 benchmark/twitter-clone/weak_datacentric/:benchmark/twitter-clone/op_mixed/ \
 benchmark/twitter-clone/mixed/:benchmark/twitter-clone/op_mixed/ \
 benchmark/twitter-clone/strong_datacentric/:benchmark/twitter-clone/op_mixed/ \
 benchmark/twitter-clone/datacentric_mixed_in_opcentric_impl/:benchmark/twitter-clone/op_mixed/
