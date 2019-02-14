package de.tudarmstadt.consistency.multinode.schema

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
@SerialVersionUID(3145521L)
class A extends Serializable {

	var f : Int = 0

	def inc(): Unit = f += 1
}
