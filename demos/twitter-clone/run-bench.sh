#!/bin/bash

CONF_PATH='local/op_mixed/'
CLASS_NAME='de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark'
JAR_NAME='target/twitter-clone-4.0.0-allinone.jar'

if [ -n "$1" ]; then
  CONF_PATH="$1"
fi

echo "Use conf path: $CONF_PATH"

java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench0.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench1.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench2.conf" &
java -cp "${JAR_NAME}" "${CLASS_NAME}" -b cassandra -c "${CONF_PATH}bench3.conf" &
wait