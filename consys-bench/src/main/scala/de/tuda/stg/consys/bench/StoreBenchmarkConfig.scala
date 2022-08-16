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
import de.tuda.stg.consys.core.store.utils.{SinglePortAddress, MultiPortAddress}
import de.tuda.stg.consys.japi.Store
import de.tuda.stg.consys.utils.InvariantUtils

import java.io.{FileNotFoundException, PrintWriter}
import scala.concurrent.duration.FiniteDuration


/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
trait StoreBenchmarkConfig {

	/** The name of the benchark, for identification purposes. */
	def name : String

	/** The underlying store for the benchmark */
	def processId : Int

	def numberOfReplicas : Int

	/** Defines how often the benchmark is repeated during warmup. */
	def warmupIterations : Int
	/** Define how ofthen the benchmark is reeated during measurements. */
	def measureIterations : Int

	/** Defines how many iterations are executed during one measurement/warmup. */
	def operationsPerIteration : Int
	/** Defines how long we wait between operations. */
	def waitBetweenOperations : FiniteDuration

	/** Defines how long the benchmark waits for each barrier */
	def barrierTimeout : FiniteDuration

	/** Defines where the measurement output is stored. */
	def outputResolver : OutputFileResolver


	/** Creates a store from this benchmark configuration */
	def createStore[StoreType <: DistributedStore with BarrierStore](storeFactory : BenchmarkStoreFactory[StoreType]) : StoreType



}


