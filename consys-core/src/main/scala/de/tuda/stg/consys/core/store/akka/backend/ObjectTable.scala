package de.tuda.stg.consys.core.store.akka.backend

import akka.cluster.ddata.{DeltaReplicatedData, ORMap, ReplicatedData, SelfUniqueAddress}

//TODO: Do we need to implement our own table?
case class ObjectTable(table : ORMap[String, ReplicatedData] = ORMap.empty) extends DeltaReplicatedData {

	override type T = ObjectTable
	override type D = Nothing


	def put(node : SelfUniqueAddress, key : String, value : ReplicatedData) : ObjectTable = {
		ObjectTable(table.put(node, key, value))
	}


	override def merge(that : T) : T =
		ObjectTable(table.merge(that.table))



	override def delta : Option[D] = ???

	override def mergeDelta(thatDelta : D) : ObjectTable = ???

	override def resetDelta : ObjectTable = ???
}
