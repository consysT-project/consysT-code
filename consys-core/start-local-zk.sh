#!/bin/bash

ZOODIR="../opt/zookeeper"

cd $ZOODIR || exit

echo "Stop server 1"
bin/zkServer.sh --config conf/server1 stop
echo "Stop server 2"
bin/zkServer.sh --config conf/server2 stop
echo "Stop server 3"
bin/zkServer.sh --config conf/server3 stop

echo "Initialize server 1"
bin/zkServer-initialize.sh --configfile=conf/server1/zoo.cfg --myid=1 --force
echo "Initialize server 2"
bin/zkServer-initialize.sh --configfile=conf/server2/zoo.cfg --myid=2 --force
echo "Initialize server 3"
bin/zkServer-initialize.sh --configfile=conf/server3/zoo.cfg --myid=3 --force

echo "Start server 1"
bin/zkServer.sh --config conf/server1 start
echo "Start server 2"
bin/zkServer.sh --config conf/server2 start
echo "Start server 3"
bin/zkServer.sh --config conf/server3 start