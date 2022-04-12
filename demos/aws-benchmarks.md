# Connect

Connect to the EC2 instance with ssh

	ssh -i ".pki/consys-benchmarks.pem" ubuntu@ec2-3-65-40-121.eu-central-1.compute.amazonaws.com


# Install consys

Clone consys

    git clone https://github.com/consysT-project/consysT-code.git
    cd consysT-code
    git checkout develop


Install Java 11

    sudo apt install openjdk-11-jdk -y

Install maven

    sudo apt install maven -y

All:

    sudo apt install openjdk-11-jdk -y
    sudo apt install maven -y
    git clone https://github.com/consysT-project/consysT-code.git
    cd consysT-code
    git checkout develop



   


# Install Cassandra

	echo "deb https://downloads.apache.org/cassandra/debian 40x main" | sudo tee -a /etc/apt/sources.list.d/cassandra.sources.list

	curl https://downloads.apache.org/cassandra/KEYS | sudo apt-key add -

	sudo apt-get update

	sudo apt-get install cassandra

	sudo service cassandra start

If necessary, you may need to add a key for installation

	sudo apt-key adv --keyserver pool.sks-keyservers.net --recv-key A278B781FE4B2BDA

Check if cassandra is running (Does this work?)

	nodetool status


## Configure Cassandra

Configuration file is found in /etc/cassandra

    sudo cp aws-bench-configs/cassandra.yaml /etc/cassandra/cassandra.yaml


## Install Cassandra via docker

	sudo apt install docker.io

	docker pull cassandra:latest

Start cassandra

	docker network create cassandra

	docker run --rm -d --name cassandra --hostname cassandra --network cassandra cassandra

	docker run --rm -it --network cassandra nuvo/docker-cqlsh cqlsh cassandra 9042 --cqlversion='3.4.4'

	docker kill cassandra

	docker network rm cassandra

# Install Zookeeper

Get configs

    git clone https://github.com/consysT-project/aws-bench-configs.git

Download Zookeeper
    
    curl https://dlcdn.apache.org/zookeeper/zookeeper-3.8.0/apache-zookeeper-3.8.0-bin.tar.gz -o zookeeper.tar.gz
    tar -xvzf zookeeper.tar.gz

Start zookeeper

    apache-zookeeper-3.8.0-bin/bin/zkServer.sh --config aws-bench-configs/zoo stop
    apache-zookeeper-3.8.0-bin/bin/zkServer.sh --config aws-bench-configs/zoo start

STart zookeeper (for myid = 1)
   
    bin/zkServer.sh --config conf/aws/server1 stop
    bin/zkServer-initialize.sh --configfile=conf/aws/server1/zoo.cfg --myid=1 --force
    bin/zkServer.sh --config conf/aws/server1 start





