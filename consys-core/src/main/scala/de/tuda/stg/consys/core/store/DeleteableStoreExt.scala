package de.tuda.stg.consys.core.store

/**
 * Created on 03.03.20.
 *
 * @author Mirko Köhler
 */
trait DeleteableStoreExt { self : Store =>

	def delete(addr : Addr) : Unit

	def clear(except : Set[Addr] = Set.empty) : Unit

}
