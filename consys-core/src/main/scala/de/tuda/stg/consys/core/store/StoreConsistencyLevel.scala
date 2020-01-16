package de.tuda.stg.consys.core.store

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait StoreConsistencyLevel extends Serializable {

	type StoreType <: Store

	def toModel(store : StoreType) : StoreConsistencyModel {type StoreType = StoreConsistencyLevel.this.StoreType}

}
