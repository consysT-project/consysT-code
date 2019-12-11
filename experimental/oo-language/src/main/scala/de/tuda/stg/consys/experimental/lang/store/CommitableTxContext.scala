package de.tuda.stg.consys.experimental.lang.store

/**
 * Created on 11.12.19.
 *
 * @author Mirko Köhler
 */
trait CommitableTxContext extends TxContext {
	def commit() : Unit
}
