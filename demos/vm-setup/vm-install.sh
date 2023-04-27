#! /bin/bash

VM_USER='eval'
ANONYMOUS_NAME='canopy'


echo "Getting repository"

apt install git -y
cd /home/$VM_USER/Desktop || exit
git clone https://github.com/consysT-project/consysT-code.git
cd /home/$VM_USER/Desktop/conysT-code || exit
git checkout vm #TODO


echo "Installing Java"

#apt install default-jre -y
apt install openjdk-11-jdk-headless -y


echo "Installing Cassandra"

apt install python3-pip -y
pip install ccm
source /home/$VM_USER/.profile

ccm create eval -v 4.0.3
ccm populate -n 4

sed -i "s/batch_size_fail_threshold_in_kb: 50/batch_size_fail_threshold_in_kb: 100/g" ~/.ccm/eval/node1/conf/cassandra.yaml
sed -i "s/batch_size_fail_threshold_in_kb: 50/batch_size_fail_threshold_in_kb: 100/g" ~/.ccm/eval/node2/conf/cassandra.yaml
sed -i "s/batch_size_fail_threshold_in_kb: 50/batch_size_fail_threshold_in_kb: 100/g" ~/.ccm/eval/node3/conf/cassandra.yaml
sed -i "s/batch_size_fail_threshold_in_kb: 50/batch_size_fail_threshold_in_kb: 100/g" ~/.ccm/eval/node4/conf/cassandra.yaml


echo "Installing Zookeeper"

cd /home/$VM_USER || exit
wget https://dlcdn.apache.org/zookeeper/zookeeper-3.6.4/apache-zookeeper-3.6.4-bin.tar.gz
tar -xf apache-zookeeper-3.6.4-bin.tar.gz -C /opt/
rm apache-zookeeper-3.6.4-bin.tar.gz
chown -R eval:eval /opt/apache-zookeeper-3.6.4-bin

mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server1
cp /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server1/zoo.cfg

mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server2
cp /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server2/zoo.cfg

mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server3
cp /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server3/zoo.cfg

mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server4
cp /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server4/zoo.cfg


echo "Installing scripts"

cp -r /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/scripts/. /home/$VM_USER/.local/bin/.


echo "Anonymizing repository"

cd /home/$VM_USER/Desktop || exit
mv consysT-code canopy-code
cd /home/$VM_USER/Desktop/canopy-code || exit

git grep -lz '' | xargs -0 sed -i -e "s/consysT/${ANONYMOUS_NAME}/g"
git grep -lz '' | xargs -0 sed -i -e "s/consys/${ANONYMOUS_NAME}/g"
git grep -lz '' | xargs -0 sed -i -e "s/de.tuda.stg/org.example.organization/g"

find . -type d -name 'de' -exec rename 's/de$/org/' {} +
find . -type d -name 'tuda' -exec rename 's/tuda$/example/' {} +
find . -type d -name 'stg' -exec rename 's/stg$/organization/' {} +

find . -depth -name '*consys*' -execdir rename "s/consys/${ANONYMOUS_NAME}/" {} +

rm -rf .git
rm .gitignore
rm logo.svg
rm -r demos/vm-setup


echo "Compiling code"

apt install maven -y

mvn package --projects demos/counter,demos/twitter-clone,demos/message-groups,demos/rubis,demos/quoddy --also-make
