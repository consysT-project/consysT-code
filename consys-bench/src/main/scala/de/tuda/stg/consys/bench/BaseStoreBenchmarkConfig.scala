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
class BaseStoreBenchmarkConfig[StoreType <: DistributedStore with BarrierStore](
	override val name : String,
	override val store : StoreType,
	override val processId : Int,
	override val numberOfReplicas : Int,
	override val warmupIterations : Int,
	override val measureIterations : Int,
	override val operationsPerIteration : Int,
	override val waitBetweenOperations : FiniteDuration,
	override val barrierTimeout : FiniteDuration,
	override val outputResolver : OutputFileResolver
) extends StoreBenchmarkConfig[StoreType] {

	def this(name : String, config : Config, storeFactory : Config => StoreType) {
		this(
			name = name,
			store = storeFactory(config),
			processId = config.getInt("consys.bench.processId"),
			numberOfReplicas = config.getInt("consys.bench.numberOfReplicas"),
			warmupIterations = config.getInt("consys.bench.warmupIterations"),
			measureIterations = config.getInt("consys.bench.measureIterations"),
			operationsPerIteration = config.getInt("consys.bench.operationsPerIteration"),
			waitBetweenOperations = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.waitPerOperation")),
			barrierTimeout = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.barrierTimeout")),
			outputResolver = new DateTimeOutputResolver(name, config.getString("consys.bench.outputPath"))
		)

		InvariantUtils.setReplicaId(processId)
		InvariantUtils.setNumOfReplicas(numberOfReplicas)
		InvariantUtils.setReplicaName(store.id.toString)

		Logger.info(s"Benchmark created: $processId of $name ready")
	}

	def this(name : String, configName : String, storeFactory : Config => StoreType) {
		this(name, ConfigFactory.load(configName), storeFactory)
	}

	override def toString : String =
		s"Benchmark($name, $store, $processId, $warmupIterations, $measureIterations, $operationsPerIteration, $waitBetweenOperations, $barrierTimeout, $outputResolver)"

}


