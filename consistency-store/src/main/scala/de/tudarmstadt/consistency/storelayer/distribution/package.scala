package de.tudarmstadt.consistency.storelayer

/**
	* Created on 14.01.19.
	*
	* @author Mirko Köhler
	*/
package object distribution {

	trait Ref[+Id, +Key, +Txid] {
		def isOp : Boolean
		def isTx : Boolean
	}

	case class OpRef[+Id, +Key](id : Id, key : Key) extends Ref[Id, Key, Nothing] {
		require(id != null)
		require(key != null)

		def toTuple : (Id, Key) =	(id, key)

		override def isOp = true
		override def isTx = false
	}

	case class TxRef[+Txid](txid : Txid) extends Ref[Nothing, Nothing, Txid] {
		require(txid != null)

		override def isOp = false
		override def isTx = true
	}

}
