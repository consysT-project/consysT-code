package de.tuda.stg.consys.core.store.akka.levels

import de.tuda.stg.consys.core.store.StoreConsistencyLevel
import de.tuda.stg.consys.core.store.akka.AkkaStore

/**
 * Created on 03.03.20.
 *
 * @author Mirko Köhler
 */
trait AkkaConsistencyLevel extends StoreConsistencyLevel {
	override type StoreType = AkkaStore
	override type Protocol = AkkaConsistencyProtocol

}
