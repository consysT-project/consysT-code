#!/bin/bash

ZOODIR="../opt/zookeeper"

cd $ZOODIR || exit

echo "Stop server 1"
bin/zkServer.sh --config conf/server1 stop
echo "Stop server 2"
bin/zkServer.sh --config conf/server2 stop
echo "Stop server 3"
bin/zkServer.sh --config conf/server3 stop