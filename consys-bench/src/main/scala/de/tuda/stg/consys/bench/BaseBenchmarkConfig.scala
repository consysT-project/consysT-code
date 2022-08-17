package de.tuda.stg.consys.bench

/**
 * Created on 29.10.19.
 *
 * @author Mirko Köhler
 */
import com.typesafe.config.{Config, ConfigFactory}
import de.tuda.stg.consys.bench.OutputResolver.{ConsoleOutputResolver, DateTimeOutputResolver}
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
class BaseBenchmarkConfig(
	override val name : String,
	val config : Config,
	val useConsoleOutput : Boolean
) extends BenchmarkConfig {

	override val processId : Int = config.getInt("consys.bench.processId")
	override val numberOfReplicas : Int = config.getInt("consys.bench.numberOfReplicas")
	override val warmupIterations : Int = config.getInt("consys.bench.warmupIterations")
	override val measureIterations : Int = config.getInt("consys.bench.measureIterations")
	override val operationsPerIteration : Int = config.getInt("consys.bench.operationsPerIteration")
	override val waitBetweenOperations : FiniteDuration = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.waitPerOperation"))
	override val barrierTimeout : FiniteDuration = BenchmarkUtils.convertDuration(config.getDuration("consys.bench.barrierTimeout"))
	override val outputResolver : OutputResolver  = {
		if (useConsoleOutput) new ConsoleOutputResolver
		else new DateTimeOutputResolver(name, config.getString("consys.bench.outputPath"))
	}


	InvariantUtils.setReplicaId(processId)
	InvariantUtils.setNumOfReplicas(numberOfReplicas)

	override def toConfig : Config = config

	override def toString : String =
		s"Benchmark($name, $processId, $warmupIterations, $measureIterations, $operationsPerIteration, $waitBetweenOperations, $barrierTimeout, $outputResolver) with config"

	override def createStore[StoreType <: DistributedStore with BarrierStore](storeFactory : BenchmarkStoreFactory[StoreType]) : StoreType =
		storeFactory.apply(config)
}

object BaseBenchmarkConfig {
	def load(name : String, configName : String, useConsoleOutput : Boolean) : BaseBenchmarkConfig =
		new BaseBenchmarkConfig(name, ConfigFactory.load(configName), useConsoleOutput)
}


