#!/bin/bash

CONF_PATH='local/weak/'
CLASS_NAME='de.tuda.stg.consys.demo.concert.ConcertBenchmark'
JAR_NAME='target/concert-tickets-3.0.0-alpha-allinone.jar'

java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench5.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench6.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench7.conf" & java -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench8.conf"