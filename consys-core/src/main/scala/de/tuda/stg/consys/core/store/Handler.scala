package de.tuda.stg.consys.core.store

import scala.language.higherKinds

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait Handler[StoreType <: Store, T <: StoreType#ObjType] {
	def resolve(tx : => StoreType#TxContext) : StoreType#RawType[T]
}
