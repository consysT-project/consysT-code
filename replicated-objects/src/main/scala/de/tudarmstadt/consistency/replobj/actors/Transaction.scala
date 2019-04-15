package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.ConsistencyLevel
import de.tudarmstadt.consistency.replobj.actors.Transaction.NestedTransaction

import scala.collection.mutable

/**
	* Created on 12.04.19.
	*
	* @author Mirko Köhler
	*/
trait Transaction {

	def consistencyLevel : ConsistencyLevel
	def txid : Long

	def contextPath : ContextPath

	def isToplevel : Boolean = getParent.isEmpty

	def getParent : Option[Transaction]

	def start(consistencyLevel : ConsistencyLevel) : Transaction = {
		new NestedTransaction(this, incAndGetSeqFor(consistencyLevel), consistencyLevel)
	}

	private val sequence : mutable.Map[ConsistencyLevel, Int] = mutable.HashMap.empty

	private def incAndGetSeqFor(level : ConsistencyLevel): Int = sequence.get(level) match {
		case None =>
			sequence.put(level, 0)
			0
		case Some(x) =>
			sequence.put(level, x + 1)
			x + 1
	}
}

object Transaction {

	@SerialVersionUID(-9453185352L)
	class ToplevelTransaction(override val txid : Long, override val consistencyLevel : ConsistencyLevel)
		extends Transaction with Serializable {

		override def contextPath : ContextPath = ContextPath(txid)
		override def getParent : Option[Transaction] = None

		override def toString : String = s"tx::$consistencyLevel|$txid"
	}

	@SerialVersionUID(-1542145564L)
	class NestedTransaction(val parent : Transaction, val seqId : Int, override val consistencyLevel : ConsistencyLevel)
		extends Transaction with Serializable {

		override def txid : Long = parent.txid

		override def contextPath : ContextPath = parent.contextPath.withSeq(consistencyLevel, seqId)
		override def getParent : Option[Transaction] = Some(parent)

		override def toString : String = parent.toString + s"::/$consistencyLevel|$seqId"
	}


}
