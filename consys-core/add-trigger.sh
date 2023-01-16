ccm node1 cqlsh -x "DROP TRIGGER IF EXISTS trigger ON consys_experimental.objects;"
ccm node1 cqlsh -x "CREATE TRIGGER trigger ON consys_experimental.objects USING 'de.tuda.stg.consys.core.store.cassandra.backend.CassandraReplicaTrigger';"
ccm node1 cqlsh;