package de.tuda.stg.consys.core.store

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait ConsistencyLevel {

	type StoreType <: Store

	def toModel(store : StoreType) : ConsistencyModel {type StoreType = ConsistencyLevel.this.StoreType}

}
