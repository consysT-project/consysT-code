package de.tuda.stg.consys.bench.legacy

/**
 * Created on 29.10.19.
 *
 * @author Mirko Köhler
 */
import com.typesafe.config.{Config, ConfigFactory}
import de.tuda.stg.consys.bench.{BenchmarkUtils, OutputFileResolver}
import de.tuda.stg.consys.core.store.utils.{SinglePortAddress, MultiPortAddress}
import de.tuda.stg.consys.japi.Store
import de.tuda.stg.consys.utils.InvariantUtils

import java.io.{FileNotFoundException, PrintWriter}


/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
abstract class DistributedBenchmark[StoreType <: Store[_,_,_,_]](
	val name : String,
	/** The address and cassandra port of this replica. */
	val address : MultiPortAddress,
	/** The total number of replicas for this benchmark. */
	val nReplicas : Int,
	/** The id of the process that owns this replica. */
	val processId : Int /* process 0 is the coordinator */ ,
	/** Defines how often the benchmark is repeated during warmup. */
	val warmupIterations : Int,
	/** Define how ofthen the benchmark is reeated during measurements. */
	val measureIterations : Int,
	/** Defines how many iterations are executed during one measurement/warmup. */
	val operationsPerIteration : Int,
	/** Defines how long we wait between operations. */
	val waitBetweenOperations : java.time.Duration,
	/** Defines where the measurement output is stored. */
	val outputResolver : OutputFileResolver,
	/** Constructs the underlying replica store **/
	val storeCreator : (MultiPortAddress, Int, BarrierSystem) => StoreType
) {
	val system : BarrierSystem = new BarrierSystem(new SinglePortAddress(address.hostname, address.port2), nReplicas)
	var store : StoreType = storeCreator(address, processId, system)

	println(s"+++++++++++ Process $processId of $getName ready")

	def this(name : String, config : Config, outputResolver : Option[OutputFileResolver],
			 storeCreator : (MultiPortAddress, Int, BarrierSystem) => StoreType) {
		this(
			name,
			MultiPortAddress.parse(config.getString("consys.bench.hostname")),
			config.getInt("consys.bench.nReplicas"),
			config.getInt("consys.bench.processId"),
			config.getInt("consys.bench.warmupIterations"),
			config.getInt("consys.bench.measureIterations"),
			config.getInt("consys.bench.operationsPerIteration"),
			config.getDuration("consys.bench.waitPerOperation"),
			outputResolver match {
				case None => new DateTimeOutputResolver(name, config.getString("consys.bench.outputFile"))
				case Some(e) => e
			},
			storeCreator
		)

		InvariantUtils.setReplicaId(processId)
		InvariantUtils.setNumOfReplicas(nReplicas)
		InvariantUtils.setReplicaName(address.toString)
	}


	def this(name : String, configName : String, outputResolver : Option[OutputFileResolver],
			 storeCreator : (MultiPortAddress, Int, BarrierSystem) => StoreType) {
		this(name, ConfigFactory.load(configName), outputResolver, storeCreator)
	}


	/** Sets up the benchmark before measuring iterations. This includes, e.g., creating data structures. */
	protected def setup() : Unit

	/** A single iteration to be measured. The iteration is repeatedly executed  */
	protected def operation() : Unit

	/** Finishes the iterations. This is measured by the run time measure as well. */
	protected def closeOperations() : Unit = { }

	/** Cleans up all data structures after the measurement. This is not measured. */
	protected def cleanup() : Unit

	protected def getName : String = "default"

	private def busyWait(ms : Long) : Unit = {
		val start = System.currentTimeMillis
		while (System.currentTimeMillis < start + ms) {}
		//		Thread.sleep(ms)
	}


	private def warmup(skipCleanup: Boolean = false) : Unit = {
		try {
			system.barrier("warmup")
			println("## START WARMUP ##")
			for (i <- 1 to warmupIterations) {
				system.barrier("setup")
				println(s"### WARMUP $i : SETUP ###")
				setup()
				system.barrier("iterations")
				println(s"### WARMUP $i : ITERATIONS ###")
				for (j <- 1 to operationsPerIteration) {
					if (!waitBetweenOperations.isZero) busyWait(waitBetweenOperations.toMillis)
					operation()
					BenchmarkUtils.printProgress(j)
				}
				closeOperations()
				BenchmarkUtils.printDone()
				system.barrier("cleanup")
				if (i < warmupIterations || !skipCleanup) {
					println(s"### WARMUP $i : CLEANUP ###")
					cleanup()
				}
			}
			system.barrier("warmup-done")
			println("## WARMUP DONE ##")
		} catch {
			case e : Exception =>
				e.printStackTrace()
				System.err.println("Warmup failed. Retry.")
		}
	}



	private def measure() : Unit = {
		system.barrier("measure")
		println("## START MEASUREMENT ##")

		val latencyWriter = new PrintWriter(outputResolver.resolveLatencyFile(processId).toFile)
		val runtimeWriter = new PrintWriter(outputResolver.resolveRuntimeFile(processId).toFile)

		try {
			latencyWriter.println("iteration,operation,ns")
			runtimeWriter.println("iteration,ns")

			for (i <- 1 to measureIterations) {
				//Setup the measurement
				system.barrier("setup")
				println(s"### MEASURE $i : SETUP ###")
				setup()

				//Run the measurement
				system.barrier("iterations")
				println(s"### MEASURE $i : OPERATIONS ###")
				val startIt = System.nanoTime()
				for (j <- 1 to operationsPerIteration) {
					if (!waitBetweenOperations.isZero) busyWait(waitBetweenOperations.toMillis)
					val startOp = System.nanoTime
					operation()
					val latency = System.nanoTime - startOp
					latencyWriter.println(s"$i,$j,$latency")
					BenchmarkUtils.printProgress(j)
				}
				closeOperations() // TODO: still necessary?
				//Measure total runtime (~ time to consistency)
				val runtime = System.nanoTime - startIt
				runtimeWriter.println(s"$i,$runtime")
				BenchmarkUtils.printDone()
				//Flush writers
				runtimeWriter.flush()
				latencyWriter.flush()

				//Cleanup the iteration
				system.barrier("cleanup")
				println(s"### MEASURE $i : CLEANUP ###")
				cleanup()
			}
		} catch {
			case e : FileNotFoundException =>
				throw new IllegalStateException("file not found", e)
			case e : Exception =>
				e.printStackTrace()
				System.err.println("Measure failed. Retry.")
		} finally {
			latencyWriter.close()
			runtimeWriter.close()
		}

		//Wait for measurement being done.
		system.barrier("measure-done")
		println("## MEASUREMENT DONE ##")
	}


	def runBenchmark() : Unit = {
		warmup()
		measure()
	}

	def runWarmupOnlyWithoutCleanup() : Unit = {
		warmup(true)
	}
}

object DistributedBenchmark {

	def start(benchmark : Class[_ <: DistributedBenchmark[_]], args : Array[String]) : Unit = {
		if (args.length == 1) {
			start(benchmark, args(0), None)
		} else if (args.length == 2) {
			start(benchmark, args(0), Some(new SimpleOutputResolver(benchmark.getSimpleName, args(1))))
		} else {
			println("Wrong usage of command. Expected: $ benchmark configFilePath [outputDirectory]")
		}
	}

	def start(benchmark : Class[_ <: DistributedBenchmark[_]], configName : String, outputResolver : Option[OutputFileResolver]) : Unit = {
		val constructor = benchmark.getConstructor(classOf[Config], classOf[Option[OutputFileResolver]])
		val bench = constructor.newInstance(ConfigFactory.load(configName), outputResolver)

		bench.runBenchmark()
	}

}
