package de.tuda.stg.consys.bench

import de.tuda.stg.consys.core.store.extensions.DistributedStore
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore
import de.tuda.stg.consys.utils.Logger

import java.io.{FileNotFoundException, PrintWriter}

class StoreBenchmarkExecutor[StoreType <: DistributedStore with BarrierStore](
	val store : StoreType,
	val config : StoreBenchmarkConfig,
	val ops : StoreBenchmarkOps
) {

	private def busyWait(ms : Long) : Unit = {
		val start = System.currentTimeMillis
		while (System.currentTimeMillis < start + ms) {}
		//		Thread.sleep(ms)
	}

	private def barrier(name : String) : Unit =
		store.barrier(name, config.numberOfReplicas, config.barrierTimeout)

	private def warmup(skipCleanup: Boolean = false) : Unit = {
		import config._
		try {
			barrier("warmup")
			Logger.info("## START WARMUP ##")
			for (i <- 1 to warmupIterations) {
				barrier("setup")
				Logger.info(s"### WARMUP $i : SETUP ###")
				ops.setup()
				barrier("iterations")
				Logger.info(s"### WARMUP $i : ITERATIONS ###")
				for (j <- 1 to operationsPerIteration) {
					if (waitBetweenOperations.toMillis > 0) busyWait(waitBetweenOperations.toMillis)
					ops.operation()
					BenchmarkUtils.printProgress(j)
				}
				ops.closeOperations()
				BenchmarkUtils.printDone()
				barrier("cleanup")
				if (i < warmupIterations || !skipCleanup) {
					Logger.info(s"### WARMUP $i : CLEANUP ###")
					ops.cleanup()
				}
			}
			barrier("warmup-done")
			Logger.info("## WARMUP DONE ##")
		} catch {
			case e : Exception =>
				e.printStackTrace()
				Logger.err("Warmup failed. Retry.")
		}
	}



	private def measure() : Unit = {
		import config._

		barrier("measure")
		Logger.info("## START MEASUREMENT ##")

		val latencyWriter = new PrintWriter(outputResolver.resolveLatencyFile(processId).toFile)
		val runtimeWriter = new PrintWriter(outputResolver.resolveRuntimeFile(processId).toFile)

		try {
			latencyWriter.println("iteration,operation,ns")
			runtimeWriter.println("iteration,ns")

			for (i <- 1 to config.measureIterations) {
				//Setup the measurement
				barrier("setup")
				Logger.info(s"### MEASURE $i : SETUP ###")
				ops.setup()

				//Run the measurement
				barrier("iterations")
				Logger.info(s"### MEASURE $i : OPERATIONS ###")
				val startIt = System.nanoTime()
				for (j <- 1 to operationsPerIteration) {
					if (waitBetweenOperations.toMillis > 0) busyWait(waitBetweenOperations.toMillis)
					val startOp = System.nanoTime
					ops.operation()
					val latency = System.nanoTime - startOp
					latencyWriter.println(s"$i,$j,$latency")
					BenchmarkUtils.printProgress(j)
				}
				ops.closeOperations() // TODO: still necessary?
				//Measure total runtime (~ time to consistency)
				val runtime = System.nanoTime - startIt
				runtimeWriter.println(s"$i,$runtime")
				BenchmarkUtils.printDone()
				//Flush writers
				runtimeWriter.flush()
				latencyWriter.flush()

				//Cleanup the iteration
				barrier("cleanup")
				Logger.info(s"### MEASURE $i : CLEANUP ###")
				ops.cleanup()
			}
		} catch {
			case e : FileNotFoundException =>
				throw new IllegalStateException("file not found", e)
			case e : Exception =>
				e.printStackTrace()
				Logger.err("Measure failed. Retry.")
		} finally {
			latencyWriter.close()
			runtimeWriter.close()
		}

		//Wait for measurement being done.
		barrier("measure-done")
		Logger.info("## MEASUREMENT DONE ##")
	}


	def runBenchmark() : Unit = {
		warmup()
		measure()
	}

	def runWarmupOnlyWithoutCleanup() : Unit = {
		warmup(true)
	}

}
