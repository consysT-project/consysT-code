#!/bin/bash

ZOODIR="../opt/zookeeper"

cd $ZOODIR || exit

bin/zkServer.sh --config conf/aws/server1 stop

bin/zkServer-initialize.sh --configfile=conf/aws/server1/zoo.cfg --myid=$1 --force

bin/zkServer.sh --config conf/aws/server1 start
