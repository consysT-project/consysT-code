#!/bin/bash

JAR_NAME='target/invariant-demos-3.0.0-alpha-allinone.jar'

CONF_PATH='local/opmixed/'

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.BankAccountBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.BankAccountLWWBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ConsensusBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.DistributedLockBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.JointBankAccountBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ReplicatedCreditAccountBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ResettableCounterBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.TournamentBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"


CONF_PATH='local/opstrong/'

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.BankAccountBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.BankAccountLWWBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ConsensusBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.DistributedLockBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.JointBankAccountBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ReplicatedCreditAccountBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.ResettableCounterBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"

CLASS_NAME='de.tuda.stg.consys.demo.invariantdemos.TournamentBenchmark'
java -Xmx2048m  -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench0.conf"\
 & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench1.conf"\
  & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench2.conf"\
   & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench3.conf"\
    & java -Xmx2048m -cp "${JAR_NAME}" "${CLASS_NAME}" "${CONF_PATH}bench4.conf"



