#!/usr/bin/bash

ZOO_DIR="/opt/apache-zookeeper-3.6.4-bin"

cd $ZOO_DIR || exit

bin/zkServer.sh --config conf/server1 status
bin/zkServer.sh --config conf/server2 status
bin/zkServer.sh --config conf/server3 status
bin/zkServer.sh --config conf/server4 status
