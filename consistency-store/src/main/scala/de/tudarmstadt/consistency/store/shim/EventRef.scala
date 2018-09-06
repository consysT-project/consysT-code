package de.tudarmstadt.consistency.store.shim

/**
	* Created on 06.09.18.
	*
	* @author Mirko Köhler
	*/
sealed trait EventRef[Id, +Key] {
	def id : Id
}

object EventRef {
	case class UpdateRef[Id, Key](id : Id, key : Key) extends EventRef[Id, Key]
	case class TxRef[Id](id : Id) extends EventRef[Id, Nothing]
}
