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
trait StoreBenchmark[StoreType <: DistributedStore with BarrierStore] {

	/** The name of the benchark, for identification purposes. */
	def name : String

	/** The underlying store for the benchmark */
	def store : StoreType

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




	/** Sets up the benchmark before measuring iterations. This includes, e.g., creating data structures. */
	protected def setup() : Unit

	/** A single iteration to be measured. The iteration is repeatedly executed  */
	protected def operation() : Unit

	/** Finishes the iterations. This is measured by the run time measure as well. */
	protected def closeOperations() : Unit = { }

	/** Cleans up all data structures after the measurement. This is not measured. */
	protected def cleanup() : Unit



	private def busyWait(ms : Long) : Unit = {
		val start = System.currentTimeMillis
		while (System.currentTimeMillis < start + ms) {}
		//		Thread.sleep(ms)
	}


	private def warmup(skipCleanup: Boolean = false) : Unit = {
		try {
			store.barrier("warmup", numberOfReplicas, barrierTimeout)
			println("## START WARMUP ##")
			for (i <- 1 to warmupIterations) {
				store.barrier("setup" , numberOfReplicas, barrierTimeout)
				println(s"### WARMUP $i : SETUP ###")
				setup()
				store.barrier("iterations", numberOfReplicas, barrierTimeout)
				println(s"### WARMUP $i : ITERATIONS ###")
				for (j <- 1 to operationsPerIteration) {
					if (waitBetweenOperations.toMillis > 0) busyWait(waitBetweenOperations.toMillis)
					operation()
					BenchmarkUtils.printProgress(j)
				}
				closeOperations()
				BenchmarkUtils.printDone()
				store.barrier("cleanup", numberOfReplicas, barrierTimeout)
				if (i < warmupIterations || !skipCleanup) {
					println(s"### WARMUP $i : CLEANUP ###")
					cleanup()
				}
			}
			store.barrier("warmup-done", numberOfReplicas, barrierTimeout)
			println("## WARMUP DONE ##")
		} catch {
			case e : Exception =>
				e.printStackTrace()
				System.err.println("Warmup failed. Retry.")
		}
	}



	private def measure() : Unit = {
		store.barrier("measure", numberOfReplicas, barrierTimeout)
		println("## START MEASUREMENT ##")

		val latencyWriter = new PrintWriter(outputResolver.resolveLatencyFile(processId).toFile)
		val runtimeWriter = new PrintWriter(outputResolver.resolveRuntimeFile(processId).toFile)

		try {
			latencyWriter.println("iteration,operation,ns")
			runtimeWriter.println("iteration,ns")

			for (i <- 1 to measureIterations) {
				//Setup the measurement
				store.barrier("setup", numberOfReplicas, barrierTimeout)
				println(s"### MEASURE $i : SETUP ###")
				setup()

				//Run the measurement
				store.barrier("iterations", numberOfReplicas, barrierTimeout)
				println(s"### MEASURE $i : OPERATIONS ###")
				val startIt = System.nanoTime()
				for (j <- 1 to operationsPerIteration) {
					if (waitBetweenOperations.toMillis > 0) busyWait(waitBetweenOperations.toMillis)
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
				store.barrier("cleanup", numberOfReplicas, barrierTimeout)
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
		store.barrier("measure-done", numberOfReplicas, barrierTimeout)
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


