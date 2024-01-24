#!/bin/bash

for i in {1..3}; do
  ./zookeeper/bin/zkServer.sh --config ./zookeeper-old/conf/server$i stop
done

for i in {1..3}; do
  ./zookeeper/bin/zkServer-initialize.sh --configfile=./zookeeper-old/conf/server$i/zoo.cfg --myid=$i --force
done

for i in {1..3}; do
  ./zookeeper/bin/zkServer.sh --config ./zookeeper-old/conf/server$i start
done

