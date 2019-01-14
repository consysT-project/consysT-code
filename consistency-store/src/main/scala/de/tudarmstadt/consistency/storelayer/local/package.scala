package de.tudarmstadt.consistency.storelayer

import de.tudarmstadt.consistency.storelayer.distribution.{OpRef, TxRef}

/**
	* Created on 14.01.19.
	*
	* @author Mirko Köhler
	*/
package object local {

	final case class OpNode[Id, Txid, Key, Data](id : Id, key : Key, data : Data, txid : Option[TxRef[Txid]], dependencies : Set[OpRef[Id, Key]])
	final case class TxNode[Id, Txid, Key](txid : Txid, dependencies : Set[OpRef[Id, Key]])

}
