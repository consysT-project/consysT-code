package de.tuda.stg.consys.bench

import de.tuda.stg.consys.core.store.extensions.DistributedStore
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore
import de.tuda.stg.consys.logging.Logger

import java.io.{FileNotFoundException, PrintWriter}

class BenchmarkExecutor(
	val config : BenchmarkConfig,
	val storeFactory : BenchmarkStoreFactory[_ <: DistributedStore with BarrierStore],
	val runnableFactory : BenchmarkRunnableFactory
) {

	private def busyWait(ms : Long) : Unit = {
		val start = System.currentTimeMillis
		while (System.currentTimeMillis < start + ms) {}
		//		Thread.sleep(ms)
	}

	private def barrier(store : BarrierStore, name : String) : Unit =
		store.barrier(name, config.numberOfReplicas, config.barrierTimeout)

	private def withStore(f : (DistributedStore with BarrierStore) => Any) : Unit = {
		var store = config.createStore(storeFactory)
		try {
			f(store)
		} finally {
			store.close()
			store = null
			System.gc()	
		}		
	}
	
	private val procName : String = "proc-" + config.processId
		
	
	private def warmup(skipCleanup: Boolean = false) : Unit = {
		import config._
		
		Logger.info(procName, "Start warmup")
		
		try {						
			for (i <- 1 to warmupIterations) {
				withStore { store =>
					// Init
					barrier(store, "warmup-initialize")
					val runnable = runnableFactory.create(store, config)

					// Setup
					barrier(store, "setup")
					Logger.info(procName, s"Warmup $i: setup")
					runnable.setup()

					// Execute
					barrier(store, "execute")
					Logger.info(procName, s"Warmup $i: iterations")
					val operations = runnable.operations

					for (j <- 1 to operationsPerIteration) {
						if (waitBetweenOperations.toMillis > 0) busyWait(waitBetweenOperations.toMillis)
						val op = operations.getOperation
						op.run()
						BenchmarkUtils.printProgress(j)
					}

					runnable.closeOperations()
					BenchmarkUtils.printDone()

					// Cleanup
					barrier(store, "cleanup")
					if (i < warmupIterations || !skipCleanup) {
						Logger.info(procName, s"Warmup $i: cleanup")
						runnable.cleanup()
					}

					// Done
					barrier(store, "warmup-done")
				}
			}			
		} catch {
			case e : Exception =>
				e.printStackTrace()
				Logger.err(procName, "Warmup failed")
		}
	}



	private def measure() : Unit = {
		import config._

		Logger.info(procName, "Start measure")

		val latencyWriter = outputResolver.latencyWriter(processId)
		val runtimeWriter = outputResolver.runtimeWriter(processId)

		try {
			latencyWriter.println("iteration,operation,ns")
			runtimeWriter.println("iteration,ns")

			for (i <- 1 to config.measureIterations) {
				withStore { store =>
					//Init
					barrier(store, "warmup-initialize")
					val runnable = runnableFactory.create(store, config)

					//Setup the measurement
					barrier(store, "setup")
					Logger.info(procName, s"Measure $i: setup")
					runnable.setup()

					//Run the measurement
					barrier(store, "iterations")
					Logger.info(procName, s"Measure $i: iterations")
					val operations = runnable.operations

					val startIt = System.nanoTime()
					for (j <- 1 to operationsPerIteration) {
						if (waitBetweenOperations.toMillis > 0) busyWait(waitBetweenOperations.toMillis)
						val op = operations.getOperation

						val startOp = System.nanoTime
						op.run()
						val latency = System.nanoTime - startOp

						latencyWriter.println(s"$i,$j,$latency")
						BenchmarkUtils.printProgress(j)
					}

					runnable.closeOperations() // TODO: still necessary?

					//Measure total runtime (~ time to consistency)
					val runtime = System.nanoTime - startIt
					runtimeWriter.println(s"$i,$runtime")
					BenchmarkUtils.printDone()

					//Flush writers
					runtimeWriter.flush()
					latencyWriter.flush()

					//Cleanup the iteration
					barrier(store, "cleanup")
					Logger.info(procName, s"Measure $i: cleanup")
					runnable.cleanup()

					//Done
					barrier(store, "measure-done")
				}
			}
		} catch {
			case e : FileNotFoundException =>
				throw new IllegalStateException("file not found", e)
			case e : Exception =>
				e.printStackTrace()
				Logger.err(procName,"Measure failed")
		} finally {
			latencyWriter.close()
			runtimeWriter.close()
		}

		//Wait for measurement being done.
		Logger.info(procName, "Measure done")
	}


	def runBenchmark() : Unit = {
		warmup()
		measure()
	}

	def runWarmupOnlyWithoutCleanup() : Unit = {
		warmup(true)
	}

}
