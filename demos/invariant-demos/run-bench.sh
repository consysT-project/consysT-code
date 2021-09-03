#!/bin/bash

CONF_PATH='local/opmixed/'
CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.BankAccountBenchmark'
#CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.BankAccountLWWBenchmark'
#CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ConsensusBenchmark'
#CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ConsensusBenchmark'
#CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.DistributedLockBenchmark'
#CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.JointBankAccountBenchmark'
#CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ReplicatedCreditAccountBenchmark'
#CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ResettableCounterBenchmark'
#CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.TournamentBenchmark'
JAR_NAME='target/invariant-demos-3.0.0-alpha-allinone.jar'

java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"
