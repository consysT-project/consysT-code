package de.tudarmstadt.consistency.store.scala.util

import scala.collection.TraversableOnce.MonadOps

/**
	* Created on 21.08.18.
	*
	* @author Mirko Köhler
	*/
/*trait Retry[T, U] extends RetryIterator with RetryChecker[T, U] {

	def compute(f : => T) : U = {
		while (next()) {
			val result : T = f

			if (validate(result)) {
				return transform(result)
			}
		}

		failed
	}
}

trait RetryIterator {
	protected def next() : Boolean
}

trait RetryChecker[T, U] {
	protected def validate(result : T) : Boolean
	protected def transform(result : T) : U
	protected def failed : U
}


object Retry {

	object Iterators {
		case class MaxIterations(n : Int) extends RetryIterator {
			private var count = n

			override protected def next() : Boolean = {
				count -= 1
				count > 0
			}
		}

		case object UntilSuccess extends RetryIterator {
			override protected def next() : Boolean =
				true
		}
	}

	def repeat(until : RetryIterator) : ApplyRetryIterator =
		ApplyRetryIterator(until)

	object Checkers {
		case class CheckPredicate[T](validate : T => Boolean) extends RetryChecker[T, Option[T]] {
			override protected def transform(result : T) : Option[T] = Some(result)
			override protected def failed : Option[T] = None
			override protected def validate(result : T) : Boolean = validate.apply(result)
		}


	}

	case class ApplyRetryIterator(it : RetryIterator) {
		def withHandler[T,U](retryChecker: RetryChecker[T,U]) : Retry[T,U] = new Retry[T,U] {
			override protected def next() : Boolean = it.next()
			override protected def validate(result : T) : Boolean = retryChecker.validate(result)
			override protected def transform(result : T) : U = retryChecker.transform(result)
			override protected def failed : U = retryChecker.failed
		}
	}

}*/
