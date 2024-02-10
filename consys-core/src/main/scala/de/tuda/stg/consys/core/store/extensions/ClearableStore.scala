package de.tuda.stg.consys.core.store.extensions

import de.tuda.stg.consys.core.store.Store

trait ClearableStore extends Store {

	def clear() : Unit

}
