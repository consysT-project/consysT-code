# OOPSLA 2020 Artifact Evaluation

## Executing the benchmarks

We have benchmarks for five case studies in the paper. 
To execute them on your local machine, you need to follow the
following steps.

There are 5 different benchmarks in the paper. 
Change your open a terminal and navigate to `demos/[benchmark-name]`.
This tutorial shows you how to execute the counter benchmark.

`$ cd demos/counter`

Run the `run-all.sh` script that is located in the benchmark 
folder.

`./run-all.sh`

This will execute the default benchmark for the `weak`, `strong` 
and `mixed` configurations.

The raw output is in folder `demos/counter/bench-results`.