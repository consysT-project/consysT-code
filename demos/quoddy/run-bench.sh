#!/bin/bash

CONF_PATH='new-local/mixed/'
CLASS_NAME='de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark'
JAR_NAME='target/quoddy-3.0.0-alpha-allinone.jar'

java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf" &
wait