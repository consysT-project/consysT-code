package de.tuda.stg.consys.objects.crdt

/**
	* Created on 05.06.19.
	*
	* @author Mirko Köhler
	*/
abstract class CrossCRDT[A, B](a : StateBasedCRDT[A], b : StateBasedCRDT[B]) extends StateBasedCRDT[(A, B)] {


	override protected [crdt] def initialState : (A, B) =
		(a.initialState, b.initialState)

	override def merge(otherState : (A, B)) : Unit = {
		a.merge(otherState._1)
		b.merge(otherState._2)
	}

}
