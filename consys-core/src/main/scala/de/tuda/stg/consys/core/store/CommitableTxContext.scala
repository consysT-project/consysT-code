package de.tuda.stg.consys.core.store

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CommitableTxContext extends TxContext {
	def commit() : Unit
}
