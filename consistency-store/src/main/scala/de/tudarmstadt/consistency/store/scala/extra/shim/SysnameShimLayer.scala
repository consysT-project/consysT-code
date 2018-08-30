package de.tudarmstadt.consistency.store.scala.extra.shim

import de.tudarmstadt.consistency.store.scala.extra.SysnameStore

/**
	* Created on 29.08.18.
	*
	* @author Mirko Köhler
	*/
trait SysnameShimLayer[Id, Key, Data, TxStatus, Consistency, Isolation] extends SysnameStore[Id, Key, Data, TxStatus, Consistency, Isolation] {

}
