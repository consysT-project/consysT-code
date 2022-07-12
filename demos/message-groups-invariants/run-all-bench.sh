#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark'
JAR_NAME='target/message-groups-3.0.0-alpha-allinone.jar'

CONF_PATH='new-local/weak/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf" &
wait

CONF_PATH='new-local/mixed/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf" &
wait

CONF_PATH='new-local/strong/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf" &
wait

