package de.tuda.stg.consys.core.store.extensions

import de.tuda.stg.consys.core.store.Store

/**
 * A store that supports deletion of objects.
 */
trait DeleteableStore extends Store {

	/** Deletes an object on the given address. */
	def delete(addr : Addr) : Unit

	/** Clears all objects except the ones on the given adresses. */
	def clear(except : Set[Addr] = Set.empty) : Unit

}
