#!/bin/bash

CONF_PATH='local/opmixed/'
CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ReplicatedCreditAccountBenchmark'
JAR_NAME='target/invariant-demos-3.0.0-alpha-allinone.jar'

java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"