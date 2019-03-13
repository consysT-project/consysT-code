package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.actors.Requests.{InvokeOp, Operation}

import scala.collection.mutable

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaMultiversionReplicatedObject[Addr, T <: AnyRef, L] {
 self : AkkaReplicatedObject[Addr, T, L] =>


	protected trait MultiversionObjectActor extends ObjectActor {

		private val opCache : mutable.Map[ContextPath, (Operation[_], Any)] = mutable.HashMap.empty

		protected def clearCache() : Unit = {
			opCache.clear()
		}

		protected def cache[R](op : Operation[R], value : R) : Unit = {
			opCache.put(op.path, (op, value)) match {
				case None => //supi
				case Some(_) => sys.error(s"cannot cache $op. already cached.")
			}
		}


		override protected def internalApplyOp[R](op : Operation[R]) : R = opCache.get(op.path) match {
			case None =>
				//not cached = apply op then cache result
				val res = super.internalApplyOp(op)
				opCache.put(op.path, (op, res))
				res

			case Some(cached) =>
				//result is cached = retrieve cache result
				val (cachedOp, res) = cached
				assert(cachedOp == op)

				println(s"cache hit with $op: $res")

				res.asInstanceOf[R]
	}

	}

}
