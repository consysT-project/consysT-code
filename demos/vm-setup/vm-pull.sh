#! /bin/bash

VM_USER='eval'
ANONYMOUS_NAME='canopy'


echo "Removing old repository"

rm -rf /home/$VM_USER/Desktop/$ANONYMOUS_NAME-code


echo "Getting repository"

cd /home/$VM_USER/Desktop || exit
sudo -u $VM_USER git clone https://github.com/consysT-project/consysT-code.git
cd /home/$VM_USER/Desktop/consysT-code || exit
git checkout vm #TODO


echo "Installing Zookeeper"

cd /home/$VM_USER || exit

sudo -u $VM_USER mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server1
cp /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server1/zoo.cfg

sudo -u $VM_USER mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server2
cp /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server2/zoo.cfg

sudo -u $VM_USER mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server3
cp /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server3/zoo.cfg

sudo -u $VM_USER mkdir -p /opt/apache-zookeeper-3.6.4-bin/conf/server4
cp /home/$VM_USER/Desktop/consysT-code/demos/vm-setup/zookeeper/conf/server1/zoo.cfg /opt/apache-zookeeper-3.6.4-bin/conf/server4/zoo.cfg


echo "Anonymizing repository"

cd /home/$VM_USER/Desktop || exit
mv consysT-code ${ANONYMOUS_NAME}-code
cd /home/$VM_USER/Desktop/${ANONYMOUS_NAME}-code || exit

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

mvn package --projects demos/counter,demos/twitter-clone,demos/message-groups,demos/rubis,demos/quoddy --also-make
