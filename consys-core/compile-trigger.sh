$echo ccm stop

$echo mvn clean package

$echo cp ./target/consys-core-4.0.0-jar-with-dependencies.jar ~/.ccm/consys_test/node1/conf/triggers
$echo cp ./target/consys-core-4.0.0-jar-with-dependencies.jar ~/.ccm/consys_test/node2/conf/triggers
$echo cp ./target/consys-core-4.0.0-jar-with-dependencies.jar ~/.ccm/consys_test/node3/conf/triggers


$echo ccm start