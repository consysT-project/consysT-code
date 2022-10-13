#!/bin/bash

CONF_PATH='local/op_mixed/'
CLASS_NAME='de.tuda.stg.consys.demo.counter.CounterBenchmark'
JAR_NAME='target/counter-4.0.0-allinone.jar'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait
