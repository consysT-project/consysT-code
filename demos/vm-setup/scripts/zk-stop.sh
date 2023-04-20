#!/usr/bin/bash

ZOODIR="/opt/apache-zookeeper-3.6.4-bin"

cd $ZOODIR || exit

bin/zkServer.sh --config conf/server1 stop
bin/zkServer.sh --config conf/server2 stop
bin/zkServer.sh --config conf/server3 stop
bin/zkServer.sh --config conf/server4 stop

