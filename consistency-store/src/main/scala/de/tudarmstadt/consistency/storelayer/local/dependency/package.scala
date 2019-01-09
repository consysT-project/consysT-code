package de.tudarmstadt.consistency.storelayer.local

/**
	* Created on 09.01.19.
	*
	* @author Mirko Köhler
	*/
package object dependency {

	//For communication with the outside world.
	case class OpNode[Id, Key, Data, Txid](id : Id, key : Key, data : Data, txid : Option[Txid], dependencies : Set[Id])
	case class TxNode[Id, Txid](txid : Txid, dependencies : Set[Id])
}
