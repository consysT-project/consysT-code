package de.tudarmstadt.consistency.replobj.actors

import scala.util.Random

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
case class ContextPath(txid : Int, sequence : List[Int] = Nil) {

	def push() : ContextPath = {
		copy(sequence = 0 :: sequence)
	}

	def pop() : ContextPath = {
		copy(sequence = sequence.tail)
	}

	def next() : ContextPath = {
		copy(sequence = (sequence.head + 1) :: sequence.tail )
	}

	def isEmpty : Boolean = sequence.isEmpty

	override def toString : String = {
		"[" + sequence.reverse.foldLeft(s"$txid::")((acc, e) => acc + "/" + e) + "]"
	}

}

object ContextPath {

	def create(head : Int) : ContextPath = ContextPath(head, Nil)


	def createFresh : ContextPath = {
		def freshId() : Int = Random.nextInt()
		create(freshId())
	}
}
