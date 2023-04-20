#! /bin/bash

echo "Installing Java"

apt install default-jre -y
apt install openjdk-11-jdk-headless -y


echo "Installing Cassandra"

apt install python3-pip -y
pip install ccm
source ~/.profile

ccm create eval -v 4.0.3
ccm populate -n 4

sed -i "s/batch_size_fail_threshold_in_kb: 50/batch_size_fail_threshold_in_kb: 100/g" ~/.ccm/eval/node1/conf/cassandra.yaml
sed -i "s/batch_size_fail_threshold_in_kb: 50/batch_size_fail_threshold_in_kb: 100/g" ~/.ccm/eval/node2/conf/cassandra.yaml
sed -i "s/batch_size_fail_threshold_in_kb: 50/batch_size_fail_threshold_in_kb: 100/g" ~/.ccm/eval/node3/conf/cassandra.yaml
sed -i "s/batch_size_fail_threshold_in_kb: 50/batch_size_fail_threshold_in_kb: 100/g" ~/.ccm/eval/node4/conf/cassandra.yaml


echo "Installing Zookeeper"

wget https://dlcdn.apache.org/zookeeper/zookeeper-3.6.4/apache-zookeeper-3.6.4-bin.tar.gz
tar -xf apache-zookeeper-3.6.4-bin.tar.gz -C /opt/
chown -R eval:eval /opt/apache-zookeeper-3.6.4-bin

mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server1
cp ~/setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server1/zoo.cfg

mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server2
cp ~/setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server2/zoo.cfg

mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server3
cp ~/setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server3/zoo.cfg

mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server4
cp ~/setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server4/zoo.cfg


echo "Installing scripts"

cp -r ~/setup/bin/. ~/.local/bin/.


echo "Installing repository"

apt install maven -y

apt install git -y
cd ~/Desktop
git clone https://github.com/consysT-project/consysT-code.git
git checkout develop

