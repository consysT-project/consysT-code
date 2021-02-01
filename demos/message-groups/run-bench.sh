#!/bin/bash

CONF_PATH='local/strong-weak/00perc-weak/'
CLASS_NAME='de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark'
JAR_NAME='target/message-groups-2.0.0-allinone.jar'

if [ -n "$1" ]; then
  CONF_PATH="$1"
fi

echo "Use conf path: $CONF_PATH"

java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench5.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench6.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench7.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench8.conf"