package de.tuda.stg.consys.experimental.lang.cassandra

import de.tuda.stg.consys.core.{ConsistencyLevel, Ref, ReplicatedObject}
import de.tuda.stg.consys.experimental.lang.LangBinding

/**
 * Created on 28.11.19.
 *
 * @author Mirko Köhler
 */
private[cassandra] case class CassandraRef[Loc, T <: LangBinding.Obj] (
	addr : Loc,
	consistencyLevel : ConsistencyLevel,
	@transient private var replicaSystem : CassandraReplicaSystem { type Addr = Loc; type Obj = LangBinding.Obj }
) extends Ref[Loc, T] {

	override def deref : ReplicatedObject[Loc, T] = ???

	override def isAvailable : Boolean = ???

	override def await() : Unit = ???

	override def delete() : Unit = ???
}
