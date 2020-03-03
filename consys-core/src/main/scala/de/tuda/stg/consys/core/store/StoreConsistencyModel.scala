package de.tuda.stg.consys.core.store

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait StoreConsistencyModel {
	type StoreType <: Store
	type Level <: StoreConsistencyLevel

	def toLevel : Level


}
