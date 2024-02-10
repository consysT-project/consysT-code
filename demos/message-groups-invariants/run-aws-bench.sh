#!/bin/bash

CLASS_NAME='de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark'
JAR_NAME='target/message-groups-3.0.0-alpha-allinone.jar'

CONF_PATH='new-aws/weak/'
echo "Use config: ${CONF_PATH}bench$1.conf"
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench$1.conf"

CONF_PATH='new-aws/mixed/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench$1.conf"

CONF_PATH='new-aws/strong/'
java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench$1.conf"

