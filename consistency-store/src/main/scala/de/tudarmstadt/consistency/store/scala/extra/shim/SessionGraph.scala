package de.tudarmstadt.consistency.store.scala.extra.shim

/**
	* Created on 30.08.18.
	*
	* @author Mirko Köhler
	*/

trait Node
case class Update(id : Id, key : Key, data : Data, deps : Set[Id]) extends Node
case class Tx()

trait SessionGraph[Id, Key, Data] {





	trait TxGraph {

	}




}
