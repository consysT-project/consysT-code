package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.actors.Requests.Operation

import scala.collection.mutable

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaCachingReplicatedObject[Addr, T <: AnyRef, L] {
 self : AkkaReplicatedObject[Addr, T, L] =>


	protected trait CachingObjectActor extends ObjectActor {

		private val opCache : mutable.Map[Operation[_], Any] = mutable.HashMap.empty

		protected def clearCache() : Unit = {
			opCache.clear()
		}


		override protected def internalApplyOp[R](op : Operation[R]) : R = {
			//TODO: Cannot match on operation only. Need operation id.


			opCache.get(op) match {
				case None =>
					val res = super.internalApplyOp(op)
					opCache.put(op, res)
					res
				case Some(cachedRes) =>
					cachedRes.asInstanceOf[R]
			}
		}

	}

}
