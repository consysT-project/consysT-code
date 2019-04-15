package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.ConsistencyLevel

import scala.collection.mutable

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
case class ContextPath(txid : Long, sequence : List[(ConsistencyLevel, Int)] = Nil) {

	def push(l : ConsistencyLevel) : ContextPath = {
		copy(sequence = (l, 0) :: sequence)
	}

	def pop() : ContextPath = {
		copy(sequence = sequence.tail)
	}

	def next() : ContextPath = {
		val (l, seqnr) = sequence.head
		copy(sequence = (l, seqnr + 1) :: sequence.tail )
	}

	def withSeq(consistencyLevel : ConsistencyLevel, seq : Int) : ContextPath = {
		copy(sequence = sequence ++ Seq((consistencyLevel, seq)) )
	}

	def isEmpty : Boolean = sequence.isEmpty

	override def toString : String = {
		"[" + sequence.reverse.foldLeft(s"$txid::")((acc, e) => acc + "/" + e._1.toString.charAt(0) + e._2 ) + "]"
	}

}

object ContextPath {

	class ContextPathBuilder(path : ContextPath) {

		def this(txid : Long) = {
			this(ContextPath(txid))
		}

		val txid : Long = path.txid

		private val seqStack : mutable.Stack[mutable.Map[ConsistencyLevel, Int]] = new mutable.Stack()
		seqStack.push(mutable.Map.empty)

		private val currSeq : mutable.Stack[(ConsistencyLevel, Int)] = new mutable.Stack()
		currSeq.elems = path.sequence


		def push(l : ConsistencyLevel) : Unit = {
			currSeq.push((l, seqStack.head(l)))
			seqStack.push(mutable.Map.empty)
		}

		def pop() : Unit = {
			require(currSeq.nonEmpty)

			currSeq.pop()
			seqStack.pop()
		}

		def nextPath(l : ConsistencyLevel) : ContextPath = {
			def increaseAndGetSeqNr() : Int = seqStack.head.get(l) match {
				case None =>
					seqStack.head(l) = 0
					0
				case Some(n) =>
					seqStack.head(l) = n + 1
					n + 1
			}

			val nextHead : (ConsistencyLevel, Int) = (l, increaseAndGetSeqNr())

			ContextPath(txid, nextHead :: currSeq.toList)
		}

		def getParentPath : ContextPath =
			ContextPath(txid, currSeq.toList)

		def getTxid : Long = txid
	}

}
