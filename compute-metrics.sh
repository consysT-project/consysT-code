#!/bin/bash

# for bench in gcounter pncounter gset twophaseset credit_account bank_account bank_account_lww joint_bank_account resettable_counter consensus distributed_lock tournament bounded_counter multi_value_register add_only_graph two_phase_graph riak_gcounter riak_pncounter riak_gset riak_twophaseset riak_orset; do
for bench in gcounter pncounter gset twophaseset credit_account bank_account bank_account_lww joint_bank_account resettable_counter consensus distributed_lock tournament multi_value_register add_only_graph two_phase_graph riak_gcounter riak_pncounter riak_gset riak_twophaseset riak_orset; do
  echo $bench
  java -cp consys-invariants/invariants-solver/lib/jml_compiler.jar:consys-invariants/invariants-solver/lib/com.microsoft.z3.jar:consys-invariants/invariants-solver/target/invariants-solver-4.0.0-jar-with-dependencies.jar de.tuda.stg.consys.invariants.solver.Main --count $bench
done
