# $echo ccm stop

$echo jar -cvf Trigger.jar cassandra.jar RMIServerInterface.scala CassandraReplicaTrigger.scala

$echo rm ~/.ccm/consys_test/node1/conf/triggers/Trigger.jar
$echo rm ~/.ccm/consys_test/node2/conf/triggers/Trigger.jar
$echo rm ~/.ccm/consys_test/node3/conf/triggers/Trigger.jar

$echo cp ./Trigger.jar ~/.ccm/consys_test/node1/conf/triggers
$echo cp ./Trigger.jar ~/.ccm/consys_test/node2/conf/triggers
$echo cp ./Trigger.jar ~/.ccm/consys_test/node3/conf/triggers

# $echo ccm start

ccm node1 cqlsh -x "DROP TRIGGER IF EXISTS trigger ON consys_experimental.objects;"
ccm node1 cqlsh -x "CREATE TRIGGER trigger ON consys_experimental.objects USING 'de.tuda.stg.consys.core.store.cassandra.backend.CassandraReplicaTrigger';"
ccm node1 cqlsh;

