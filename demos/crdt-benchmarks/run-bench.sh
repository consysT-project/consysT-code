#!/bin/bash

CONF_PATH=''
CLASS_NAME='de.tuda.stg.consys.demo.crdts.invariants.crdts.GCounterBench'
JAR_NAME='target/crdt-benchmarks-4.0.0-allinone.jar'

java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}local0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}local1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}local2.conf" &
wait
