#!/usr/bin/bash

ZOODIR="/opt/apache-zookeeper-3.6.4-bin"

cd $ZOODIR || exit

bin/zkServer.sh --config conf/server1 stop
bin/zkServer.sh --config conf/server2 stop
bin/zkServer.sh --config conf/server3 stop
bin/zkServer.sh --config conf/server4 stop

pkill -f apache-zookeeper # just in case

bin/zkServer-initialize.sh --configfile=conf/server1/zoo.cfg --myid=1 --force
bin/zkServer-initialize.sh --configfile=conf/server2/zoo.cfg --myid=2 --force
bin/zkServer-initialize.sh --configfile=conf/server3/zoo.cfg --myid=3 --force
bin/zkServer-initialize.sh --configfile=conf/server4/zoo.cfg --myid=4 --force

bin/zkServer.sh --config conf/server1 start
bin/zkServer.sh --config conf/server2 start
bin/zkServer.sh --config conf/server3 start
bin/zkServer.sh --config conf/server4 start
