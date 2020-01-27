package de.tuda.stg.consys.core.store.binding

import de.tuda.stg.consys.core.ReplicaSystem
import de.tuda.stg.consys.core.store.Store

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
trait ReplicaSystemBinding extends ReplicaSystem {

	type StoreType <: Store {
		type Addr <: ReplicaSystemBinding.this.Addr
		type ObjType <: ReplicaSystemBinding.this.Obj
	}

	val store : StoreType

}
