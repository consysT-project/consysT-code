package de.tudarmstadt.consistency

/**
	* Created on 03.09.18.
	*
	* @author Mirko Köhler
	*/
package object store {

	trait StoreOps[Key, TxStatus, Isolation, Consistency] {
		val txStatuses : TxStatuses[TxStatus]
		val isolationLevels : IsolationLevels[Isolation]
		val consistencyLevels : ConsistencyLevels[Consistency]
	}

	trait TxStatuses[T] {
		val PENDING : T
		val COMMITTED : T
		val ABORTED : T
	}

	trait IsolationLevels[T] {
		//Snapshot isolation
		val SI : T

		//Read uncommitted
		val RU : T

		//Read committed
		val RC : T

		//None: The transaction does not provide any transactional guarantees and cannot be aborted.
		val NONE : T
	}

	trait ConsistencyLevels[T] {
		val CAUSAL : T
		val WEAK : T
		val LOCAL : T
	}


	trait Ids[T] {
		def freshId() : T
	}




}
