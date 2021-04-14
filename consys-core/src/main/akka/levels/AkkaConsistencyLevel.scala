package de.tuda.stg.consys.core.store.akka.levels

import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.akka.AkkaStore

/**
 * Created on 03.03.20.
 *
 * @author Mirko Köhler
 */
trait AkkaConsistencyLevel extends ConsistencyLevel {
	override type StoreType = AkkaStore
	override type Protocol = AkkaConsistencyProtocol

}
