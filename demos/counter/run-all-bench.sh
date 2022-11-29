#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.counter.CounterBenchmark'
JAR_NAME='target/counter-4.0.0-allinone.jar'

printf "~~ COUNTER WEAK\n\n"
CONF_PATH='local/weak/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ COUNTER OP-MIXED\n\n"
CONF_PATH='local/op_mixed/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ COUNTER MIXED\n\n"
CONF_PATH='local/mixed/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ COUNTER STRONG\n\n"
CONF_PATH='local/strong/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait
