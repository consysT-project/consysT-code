package de.tudarmstadt.consistency

import com.datastax.driver.core.Cluster
import de.tudarmstadt.consistency.store.shim.EventRef
import de.tudarmstadt.consistency.store.shim.EventRef.TxRef

/**
	* Created on 03.09.18.
	*
	* @author Mirko Köhler
	*/
package object store {

	trait StoreOps[Key, TxStatus, Isolation, Consistency] {
		val keys : Keys[Key]
		val txStatuses : TxStatuses[TxStatus]
		val isolationLevels : IsolationLevels[Isolation]
		val consistencyLevels : ConsistencyLevels[Consistency]
	}

	trait Keys[T] {
		val transactionKey : T
	}

	trait TxStatuses[T] {
		val pending : T
		val committed : T
		val aborted : T
	}

	trait IsolationLevels[T] {
		val snapshotIsolation : T
		val readUncommitted : T
		val readCommitted : T
		val none : T
	}

	trait ConsistencyLevels[T] {
		val causal : T
		val weak : T
	}





	trait Ids[T] {
		def freshId() : T
	}




}
