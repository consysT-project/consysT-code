package de.tudarmstadt.consistency.store.scala.extra.shim
import de.tudarmstadt.consistency.store.scala.extra.StoreInterface
import de.tudarmstadt.consistency.store.scala.extra.Util._

/**
	* Created on 31.08.18.
	*
	* @author Mirko Köhler
	*/
class SysnameVersionedStoreImpl[Id, Key, Data, Isolation, Consistency] (
	override val baseStore : StoreInterface[Key, Data, CassandraTxParams[Id, Isolation], CassandraOpParams[Id, Consistency]]
)(
	override val idOps : IdOps[Id],
	override val isolationLevelOps : IsolationLevelOps[Isolation],
	override val consistencyLevelOps : ConsistencyLevelOps[Consistency]
) extends SysnameVersionedStore[Id, Key, Data, Isolation, Consistency]
