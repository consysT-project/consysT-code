package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem.{InvokeOp, Operation}

import scala.collection.mutable

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
trait AkkaMultiversionReplicatedObject[Addr, T <: AnyRef, L] {
 self : AkkaReplicatedObject[Addr, T, L] =>


	protected trait MultiversionObjectActor extends ObjectActor {

		private val opCache : mutable.Map[Operation[_], Any] = mutable.HashMap.empty

		protected def clearCache() : Unit = {
			opCache.clear()
		}


		override protected def internalApplyOp[R](op : Operation[R]) : R = op match {
			case InvokeOp(id, mthdName, args) =>
				replicaSystem.log(s"invoking method $op in context ${replicaSystem.Context.getCurrentContext}")
				replicaSystem.Context.enterCtx()
				val res = super.internalApplyOp(op)
				replicaSystem.Context.leaveCtx()
				res

			case x => super.internalApplyOp(x)
		}

	}

}
