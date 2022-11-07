#!/usr/bin/env sh

CONF=$1

#echo "counter weak"
#java -cp demos/counter/target/counter-4.0.0-allinone.jar de.tuda.stg.consys.demo.counter.CounterBenchmark -b cassandra -c aws/weak/${CONF}
#echo "counter strong"
#java -cp demos/counter/target/counter-4.0.0-allinone.jar de.tuda.stg.consys.demo.counter.CounterBenchmark -b cassandra -c aws/strong/${CONF}
#echo "counter op_mixed"
#java -cp demos/counter/target/counter-4.0.0-allinone.jar de.tuda.stg.consys.demo.counter.CounterBenchmark -b cassandra -c aws/op_mixed/${CONF}
#echo "counter mixed"
#java -cp demos/counter/target/counter-4.0.0-allinone.jar de.tuda.stg.consys.demo.counter.CounterBenchmark -b cassandra -c aws/mixed/${CONF}
#
#echo "messagegroups weak"
#java -cp demos/message-groups/target/message-groups-4.0.0-allinone.jar de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark -b cassandra -c aws/weak/${CONF}
echo "messagegroups strong"
java -cp demos/message-groups/target/message-groups-4.0.0-allinone.jar de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark -b cassandra -c aws/strong/${CONF}
echo "messagegroups op_mixed"
java -cp demos/message-groups/target/message-groups-4.0.0-allinone.jar de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark -b cassandra -c aws/op_mixed/${CONF}
echo "messagegroups mixed"
java -cp demos/message-groups/target/message-groups-4.0.0-allinone.jar de.tuda.stg.consys.demo.messagegroups.MessageGroupsBenchmark -b cassandra -c aws/mixed/${CONF}

echo "twitter weak"
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/weak/${CONF}
echo "twitter strong"
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/strong/${CONF}
echo "twitter op_mixed"
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/op_mixed/${CONF}
echo "twitter mixed"
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/mixed/${CONF}
echo "twitter weak_data"
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/weak_datacentric/${CONF}
echo "twitter strong_data"
java -cp demos/twitter-clone/target/twitter-clone-4.0.0-allinone.jar de.tuda.stg.consys.demo.twitterclone.TwitterCloneBenchmark -b cassandra -c aws/strong_datacentric/${CONF}

echo "quoddy weak"
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/weak/${CONF}
echo "quoddy strong"
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/strong/${CONF}
echo "quoddy op_mixed"
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/op_mixed/${CONF}
echo "quoddy mixed"
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/mixed/${CONF}
echo "quoddy weak_data"
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/weak_datacentric/${CONF}
echo "quoddy strong data"
java -cp demos/quoddy/target/quoddy-4.0.0-allinone.jar de.tuda.stg.consys.demo.quoddy.QuoddyBenchmark -b cassandra -c aws/strong_datacentric/${CONF}

echo "rubis weak"
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/weak/${CONF}
echo "rubis strong"
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/strong/${CONF}
echo "rubis op_mixed"
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/op_mixed/${CONF}
echo "rubis mixed"
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/mixed/${CONF}
echo "rubis weak_data"
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/weak_datacentric/${CONF}
echo "rubis strong_data"
java -cp demos/rubis/target/rubis-4.0.0-allinone.jar de.tuda.stg.consys.demo.rubis.RubisBenchmark -b cassandra -c aws/strong_datacentric/${CONF}