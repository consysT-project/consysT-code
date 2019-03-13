package de.tudarmstadt.consistency.replobj.actors

import scala.util.Random

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
//trait Context {
//
//	private var path : ContextPath = emptyPath
//	private var currentSeq : Int = 0
//
//	def isEmpty : Boolean = head.isEmpty && sequence.isEmpty
//
//	def head : Option[Int] = path._1
//
//	def sequence : List[Int] = path._2
//
//
//	def getPath : ContextPath = path
//
//	def getNextPath : ContextPath = path.copy(_2 = currentSeq :: sequence)
//
//
//	def create(head : Int) : Unit = {
//		require(isEmpty)
//
//		currentSeq = 0
//		path = (Some(head), Nil)
//	}
//
//	def createFresh() : Unit = {
//		create(freshId())
//	}
//
//	private	def freshId() : Int = Random.nextInt()
//
//
//	def leave() : Unit = {
//		require(head.nonEmpty)
//		require(sequence.isEmpty)
//
//		path = emptyPath
//	}
//
//	def push() : Unit = {
//		require(head.nonEmpty)
//
//		path = path.copy(_2 = currentSeq :: sequence)
//		currentSeq = 0
//	}
//
//	def pop() : Unit = {
//		require(head.nonEmpty)
//		require(sequence.nonEmpty)
//
//		currentSeq = path._2.head
//		path = path.copy(_2 = sequence.tail)
//	}
//
//	def next() : Unit = {
//		currentSeq += 1
//	}
//
//
//
//
//
//
////	protected val toplevel : Option[OpId]
////
////	protected val path : List[SeqId]
////
////	def push(seq : Int) : ContextPath = {
////		require(toplevel.nonEmpty)
////		ContextPathImpl(toplevel, seq :: path)
////	}
////
////	def pop() : ContextPath = path match {
////		case Nil if toplevel.isEmpty => EmptyPath
////		case hd :: tl => ContextPathImpl(toplevel, tl)
////	}
////
////	def isEmpty = false
//
//}
//

case class ContextPath(head : Int, sequence : List[Int] = Nil) {

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
		"[" + sequence.reverse.foldLeft(s"$head::")((acc, e) => acc + "/" + e) + "]"
	}

}

object ContextPath {

	def create(head : Int) : ContextPath = ContextPath(head, Nil)


	def createFresh : ContextPath = {
		def freshId() : Int = Random.nextInt()
		create(freshId())
	}



//	@inline private final type OpId = Int
//	@inline private final type SeqId = Int
//
//	private object EmptyPath extends ContextPath {
//		override protected val toplevel : Option[Int] = None
//		override protected val path : List[Int] = Nil
//
//		override def isEmpty : Boolean = true
//	}
//
//	def empty : ContextPath = EmptyPath
//
//	private case class ContextPathImpl(toplevel : Option[OpId], path : List[SeqId]) extends ContextPath {
//		require(toplevel.nonEmpty || path.isEmpty)
//	}



}
