package de.tuda.stg.consys.core.store

/**
 * A consistency level that can be used with a store.
 */
trait StoreConsistencyLevel extends Serializable {

	/** The type of stores for which this consistency level is for. */
	type StoreType <: Store
	/** The consistency model for this level. */
	type Protocol <: StoreConsistencyProtocol {type StoreType = StoreConsistencyLevel.this.StoreType}

	/**
	 * Produces a consistency model for this level for a concrete store.
	 * The model implements the consistency protocol.
	 *
	 * @param store The store for which to create the model.
	 * @return A model that implements this consistency level.
	 */
	def toProtocol(store : StoreType) : Protocol

}
