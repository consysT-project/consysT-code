package de.tuda.stg.consys.bench

/**
 * Created on 29.10.19.
 *
 * @author Mirko Köhler
 */
import com.typesafe.config.{Config, ConfigFactory}
import de.tuda.stg.consys.bench.OutputFileResolver.{DateTimeOutputResolver, SimpleOutputResolver}
import de.tuda.stg.consys.core.store.utils.Address
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems
import de.tuda.stg.consys.japi.legacy.impl.akka.JAkkaReplicaSystem
import java.io.{FileNotFoundException, PrintWriter}
import scala.collection.JavaConverters


/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
abstract class DistributedBenchmark(
	/** The address of this replica. */
	val address : Address,
	/** The addresses of the other replicas. Can contain this replica. */
	val replicas : Array[Address],
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
	val outputResolver : OutputFileResolver
) {

	def system : JAkkaReplicaSystem = JReplicaSystems.getSystem

	println("All replicas found")

	def this(config : Config, outputResolver : Option[OutputFileResolver]) {
		this(
			Address.parse(config.getString("consys.bench.hostname")),
			config.getStringList("consys.bench.otherReplicas").stream().map[Address](str => Address.parse(str)).toArray(i => new Array[Address](i)),
			config.getInt("consys.bench.processId"),
			config.getInt("consys.bench.warmupIterations"),
			config.getInt("consys.bench.measureIterations"),
			config.getInt("consys.bench.operationsPerIteration"),
			config.getDuration("consys.bench.waitPerOperation"),
			outputResolver match {
				case None => new DateTimeOutputResolver(config.getString("consys.bench.outputFile"))
				case Some(e) => e
			}
		)
	}


	def this(configName : String, outputResolver : Option[OutputFileResolver]) {
		this(ConfigFactory.load(configName), outputResolver)
	}


	/** Sets up the benchmark before measuring iterations. This includes, e.g., creating data structures. */
	protected def setup() : Unit

	/** A single iteration to be measured. The iteration is repeatedly executed  */
	protected def operation() : Unit

	/** Finishes the iterations. This is measured by the run time measure as well. */
	protected def closeOperations() : Unit = { }

	/** Cleansup all datastructure after the measurement. This is not measured. */
	protected def cleanup() : Unit

	private def busyWait(ms : Long) : Unit = {
		val start = System.currentTimeMillis
		while (System.currentTimeMillis < start + ms) {}
//		Thread.sleep(ms)
	}


	private def warmup() : Unit = {
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
				println(s"### WARMUP $i : CLEANUP ###")
				cleanup()
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
				closeOperations()
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
		JReplicaSystems.withActorSystem(
			address,
			JavaConverters.asJavaIterable(replicas),
			java.time.Duration.ofSeconds(30000)
		).use(() => {
			warmup()
			measure()
		})
	}
}

object DistributedBenchmark {

	def start(benchmark : Class[_ <: DistributedBenchmark], args : Array[String]) : Unit = {
		if (args.length == 1) {
			start(benchmark, args(0), None)
		} else if (args.length == 2) {
			start(benchmark, args(0), Some(new SimpleOutputResolver(args(1))))
		} else {
			println("Wrong usage of command. Expected: $ benchmark configFilePath [outputDirectory]")
		}
	}

	def start(benchmark : Class[_ <: DistributedBenchmark], configName : String, outputResolver : Option[OutputFileResolver]) : Unit = {
		val constructor = benchmark.getConstructor(classOf[Config], classOf[Option[OutputFileResolver]])
		val bench = constructor.newInstance(ConfigFactory.load(configName), outputResolver)

		bench.runBenchmark()
	}

}
