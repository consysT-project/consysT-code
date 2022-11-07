#!/usr/bin/env sh

CONF=$1

java -cp demos/counter/target/counter-4.0.0-allinone.jar de.tuda.stg.consys.demo.counter.CounterBenchmark -b cassandra -c aws/weak/${CONF}
java -cp demos/counter/target/counter-4.0.0-allinone.jar de.tuda.stg.consys.demo.counter.CounterBenchmark -b cassandra -c aws/strong/${CONF}
java -cp demos/counter/target/counter-4.0.0-allinone.jar de.tuda.stg.consys.demo.counter.CounterBenchmark -b cassandra -c aws/op_mixed/${CONF}
java -cp demos/counter/target/counter-4.0.0-allinone.jar de.tuda.stg.consys.demo.counter.CounterBenchmark -b cassandra -c aws/mixed/${CONF}

java -cp demos/message-groups/target/message-groups-4.0.0-allinone.jar de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark -b cassandra -c aws/weak/${CONF}
java -cp demos/message-groups/target/message-groups-4.0.0-allinone.jar de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark -b cassandra -c aws/strong/${CONF}
java -cp demos/message-groups/target/message-groups-4.0.0-allinone.jar de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark -b cassandra -c aws/op_mixed/${CONF}
java -cp demos/message-groups/target/message-groups-4.0.0-allinone.jar de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark -b cassandra -c aws/mixed/${CONF}

java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/weak/${CONF}
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/strong/${CONF}
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/op_mixed/${CONF}
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/mixed/${CONF}
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/weak_datacentric/${CONF}
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/strong_datacentric/${CONF}

java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/weak/${CONF}
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/strong/${CONF}
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/op_mixed/${CONF}
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/mixed/${CONF}
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/weak_datacentric/${CONF}
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/strong_datacentric/${CONF}

java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/weak/${CONF}
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/strong/${CONF}
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/op_mixed/${CONF}
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/mixed/${CONF}
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/weak_datacentric/${CONF}
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/strong_datacentric/${CONF}