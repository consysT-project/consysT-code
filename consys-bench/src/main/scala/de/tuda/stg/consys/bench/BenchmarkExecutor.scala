package de.tuda.stg.consys.bench

import de.tuda.stg.consys.core.store.extensions.DistributedStore
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore
import de.tuda.stg.consys.utils.Logger

import java.io.{FileNotFoundException, PrintWriter}

class BenchmarkExecutor(
	val store : DistributedStore with BarrierStore,
	val config : BenchmarkConfig,
	val ops : BenchmarkOperation
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
			Logger.info(store.id, "Start warmup")
			for (i <- 1 to warmupIterations) {
				barrier("setup")
				Logger.info(store.id, s"Warmup $i: setup")
				ops.setup()
				barrier("iterations")
				Logger.info(store.id,s"Warmup $i: iterations")
				for (j <- 1 to operationsPerIteration) {
					if (waitBetweenOperations.toMillis > 0) busyWait(waitBetweenOperations.toMillis)
					ops.operation()
					BenchmarkUtils.printProgress(j)
				}
				ops.closeOperations()
				BenchmarkUtils.printDone()
				barrier("cleanup")
				if (i < warmupIterations || !skipCleanup) {
					Logger.info(store.id,s"Warmup $i: cleanup")
					ops.cleanup()
				}
			}
			barrier("warmup-done")
			Logger.info(store.id, "Warmup done")
		} catch {
			case e : Exception =>
				e.printStackTrace()
				Logger.err(store.id, "Warmup failed")
		}
	}



	private def measure() : Unit = {
		import config._

		barrier("measure")
		Logger.info(store.id,"Start measure")

		val latencyWriter = outputResolver.latencyWriter(processId)
		val runtimeWriter = outputResolver.runtimeWriter(processId)

		try {
			latencyWriter.println("iteration,operation,ns")
			runtimeWriter.println("iteration,ns")

			for (i <- 1 to config.measureIterations) {
				//Setup the measurement
				barrier("setup")
				Logger.info(store.id,s"Measure $i: setup")
				ops.setup()

				//Run the measurement
				barrier("iterations")
				Logger.info(store.id, s"Measure $i: iterations")
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
				Logger.info(store.id,s"Measure $i: cleanup")
				ops.cleanup()
			}
		} catch {
			case e : FileNotFoundException =>
				throw new IllegalStateException("file not found", e)
			case e : Exception =>
				e.printStackTrace()
				Logger.err(store.id,"Measure failed")
		} finally {
			latencyWriter.close()
			runtimeWriter.close()
		}

		//Wait for measurement being done.
		barrier("measure-done")
		Logger.info(store.id, "Measure done")
	}


	def runBenchmark() : Unit = {
		warmup()
		measure()
	}

	def runWarmupOnlyWithoutCleanup() : Unit = {
		warmup(true)
	}

}
