# Readme

## Cassandra

To use the Cassandra store integration, you first need to start Cassandra on your system. The following steps
explain how to start Cassandra on a local system.

### Initialize Cassandra

These steps have to be done to initialize Cassandra. The initialization only has to be done once. 
If Cassandra is already initialized, you can jump to Start Cassandra.

1. Initialize Cassandra using ccm. 
    `ccm create -n 3 --install-dir=./opt/cassandra test_cluster` 
    Make sure that the install dir contains a Cassandra 4+ installation.
2. That's it. Starting Cassandra is specified in the next section.

### Start Cassandra 

1. Start Cassandra. If you use ccm then create a cluster and start it with `ccm start` if the cluster
you want to start is the current cluster or `ccm start test_cluster` if you need to give a name to
the cluster. 
Ensure that you are using Casandra 4.0+ as older versions will not work with Java 11.
2. Adapt the `consys.conf` in `src/main/resources` accordingly. The ports and addresses have
to be entered correctly.
3. Be happy.


## Zookeeper

To use the Zookeeper integration, you have to start Zookeeper. The provided Zookeeper installation in `opt/zookeeper` 
already contains config files to start Zookeeper locally.

### Installation

As the Zookeeper distributed lock implementation is not deployed in Maven central, you have to install it
manually.

1. Got to `opt/zookeeper/zookeeper-recipes`.
2. Run `mvn install`.

### Initialize Zookeeper

1. Open a terminal in `opt/zookeeper`. 
2. Initialize the servers with 
    1. `bin/zkServer-initialize.sh --configfile=conf/server1/zoo.cfg --myid=1 --force`
    2. `bin/zkServer-initialize.sh --configfile=conf/server2/zoo.cfg --myid=2 --force`
    3. `bin/zkServer-initialize.sh --configfile=conf/server3/zoo.cfg --myid=3 --force`
    
### Start Zookeeper

1. Start the Zookeeper servers with `bin/zkServer.sh --config conf/server1 start` (respectively for 2 and 3).
