package de.tuda.stg.consys.bench

/**
 * Created on 29.10.19.
 *
 * @author Mirko Köhler
 */
import com.typesafe.config.{Config, ConfigFactory}
import de.tuda.stg.consys.bench.OutputFileResolver.DateTimeOutputResolver
import de.tuda.stg.consys.bench.legacy.BarrierSystem
import de.tuda.stg.consys.core.store.extensions.DistributedStore
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore
import de.tuda.stg.consys.core.store.utils.MultiPortAddress
import de.tuda.stg.consys.utils.{InvariantUtils, Logger}

import java.io.{FileNotFoundException, PrintWriter}
import scala.concurrent.duration.FiniteDuration


/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
class BaseStoreBenchmarkConfig(
	override val name : String,
	val config : Config
) extends StoreBenchmarkConfig {

	override val processId : Int = config.getInt("consys.bench.processId")
	override val numberOfReplicas : Int = config.getInt("consys.bench.numberOfReplicas")
	override val warmupIterations : Int = config.getInt("consys.bench.warmupIterations")
	override val measureIterations : Int = config.getInt("consys.bench.measureIterations")
	override val operationsPerIteration : Int = config.getInt("consys.bench.operationsPerIteration")
	override val waitBetweenOperations : FiniteDuration = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.waitPerOperation"))
	override val barrierTimeout : FiniteDuration = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.barrierTimeout"))
	override val outputResolver : OutputFileResolver  = new DateTimeOutputResolver(name, config.getString("consys.bench.outputPath"))

	InvariantUtils.setReplicaId(processId)
	InvariantUtils.setNumOfReplicas(numberOfReplicas)
//TODO: Do we need this?		InvariantUtils.setReplicaName(store.id.toString)


	override def toString : String =
		s"Benchmark($name, $processId, $warmupIterations, $measureIterations, $operationsPerIteration, $waitBetweenOperations, $barrierTimeout, $outputResolver) with config"

	override def createStore[StoreType <: DistributedStore with BarrierStore](storeFactory : BenchmarkStoreFactory[StoreType]) : StoreType =
		storeFactory.apply(config)
}

object BaseStoreBenchmarkConfig {
	def load(name : String, configName : String) : BaseStoreBenchmarkConfig =
		new BaseStoreBenchmarkConfig(name, ConfigFactory.load(configName))
}


