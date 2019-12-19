package de.tuda.stg.consys.experimental.lang.cassandra

import de.tuda.stg.consys.core.ConsistencyLevel

/**
 * Created on 28.11.19.
 *
 * @author Mirko Köhler
 */
object CassandraDemo extends App {
	import de.tuda.stg.consys.experimental.lang.LangBinding._

	var replicaSystem : CassandraReplicaSystem = _
		try {
			replicaSystem = CassandraReplicaSystemFactory.create()
			replicaSystem.replicate("test", obj(Map(), Map()), ConsistencyLevel.Weak)
			println("done")
		} finally {
			if (replicaSystem != null) replicaSystem.close()
		}
}
