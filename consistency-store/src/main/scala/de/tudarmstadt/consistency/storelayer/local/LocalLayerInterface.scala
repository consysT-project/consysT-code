package de.tudarmstadt.consistency.storelayer.local

import de.tudarmstadt.consistency.storelayer.distribution.SessionService
import de.tudarmstadt.consistency.storelayer.local.LocalLayerInterface.AbortedException
import de.tudarmstadt.consistency.storelayer.local.exceptions.{UnsupportedConsistencyLevelException, UnsupportedIsolationLevelException}

/**
	* Created on 25.01.19.
	*
	* @author Mirko Köhler
	*/
trait LocalLayerInterface[Key, Data, Isolation, Consistency] {

	val store : SessionService[_, _, Key, Data, _, Isolation, Consistency]


	trait TransactionCtx {

		def read(consistency : Consistency, key : Key) : Option[Data]

		def write(consistency : Consistency, key : Key, data : Data) : Unit

		@throws(clazz = classOf[AbortedException])
		final def abort() : Unit = throw new AbortedException
	}


	protected def createCtx(isolation : Isolation) : TransactionCtx =
		throw new UnsupportedIsolationLevelException[Isolation](isolation)


	final def transaction[B](isolation : Isolation)(f : TransactionCtx => B) : Option[B] = {
		val ctx = createCtx(isolation)

		try {
			val b = f(ctx)
			return Some(b)
		} catch {
			case _ : AbortedException =>
				return None
		}
	}
}

object LocalLayerInterface {
	/* thrown when the transaction is aborted */
	private[local] class AbortedException extends RuntimeException("the transaction has been aborted")
}
