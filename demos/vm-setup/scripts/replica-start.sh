echo "Stopping Cassandra:"
ccm stop
kill $(lsof -nPti @127.0.0.1:7000) # just in case

echo "Starting Cassandra:"
ccm setlog ERROR
ccm start

echo "Starting Zookeeper:"
zk-start.sh

replica-status.sh
