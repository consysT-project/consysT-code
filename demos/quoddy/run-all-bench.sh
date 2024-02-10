#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark'
JAR_NAME='target/quoddy-4.0.0-allinone.jar'

printf "~~ QUODDY WEAK\n\n"
CONF_PATH='local/weak/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ QUODDY OP_MIXED\n\n"
CONF_PATH='local/op_mixed/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ QUODDY MIXED\n\n"
CONF_PATH='local/mixed/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ QUODDY STRONG\n\n"
CONF_PATH='local/strong/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ QUODDY WEAK_DATACENTRIC\n\n"
CONF_PATH='local/weak_datacentric/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ QUODDY STRONG_DATACENTRIC\n\n"
CONF_PATH='local/strong_datacentric/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait

printf "~~ QUODDY DATACENTRIC_MIXED_IN_OPCENTRIC_IMPL\n\n"
CONF_PATH='local/datacentric_mixed_in_opcentric_impl/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait
