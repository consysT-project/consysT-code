package de.tuda.stg.consys.core.store

import scala.reflect.ClassTag
import scala.reflect.runtime.universe._

/**
 * A consistency model implements a protocol that is used in combinmation
 * with a store to fulfill a certain consistency level.
 */
trait StoreConsistencyProtocol {
	/** The type of stores for which this protocol implementation holds. */
	type StoreType <: Store
	/** The type of levels that are implemented with this protocol. */
	type Level <: StoreConsistencyLevel

	/** Returns the level for which this protocol holds. */
	def toLevel : Level


}
