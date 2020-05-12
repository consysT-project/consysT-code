package de.tuda.stg.consys.bench

/**
 * Created on 29.10.19.
 *
 * @author Mirko Köhler
 */
import java.io.{FileNotFoundException, IOException, PrintWriter}
import java.nio.file.{Files, Paths}
import java.text.SimpleDateFormat
import java.util.Date

import com.typesafe.config.{Config, ConfigFactory}
import de.tuda.stg.consys.core.Address
import de.tuda.stg.consys.japi.impl.JReplicaSystems
import de.tuda.stg.consys.japi.impl.akka.JAkkaReplicaSystem

import scala.collection.JavaConverters
import scala.concurrent.duration.Duration


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
	val outputFileName : String
) {
	//Important: create the followers before creating the coordinator
//	final protected var replicaSystem : JAkkaReplicaSystem = JReplicaSystems.fromActorSystem(
//		address,
//		JavaConverters.asJavaIterable(replicas),
//		java.time.Duration.ofSeconds(30000)
//	)

	def system : JAkkaReplicaSystem = JReplicaSystems.getSystem

	println("All replicas found")


	def this(config : Config) {
		this(
			Address.parse(config.getString("consys.bench.hostname")),
			config.getStringList("consys.bench.otherReplicas").stream().map[Address](str => Address.parse(str)).toArray(i => new Array[Address](i)),
			config.getInt("consys.bench.processId"),
			config.getInt("consys.bench.warmupIterations"),
			config.getInt("consys.bench.measureIterations"),
			config.getInt("consys.bench.operationsPerIteration"),
			config.getDuration("consys.bench.waitPerOperation"),
			config.getString("consys.bench.outputFile")
		)
	}


	def this(configName : String) {
		this(ConfigFactory.load(configName))
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
//		val start = System.currentTimeMillis
//		while (System.currentTimeMillis < start + ms) {}
		Thread.sleep(ms)
	}


	private def warmup() : Unit = {
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
	}


	private def measure() : Unit = {
		system.barrier("measure")
		println("## START MEASUREMENT ##")
		val sdf = new SimpleDateFormat("YY-MM-dd_kk-mm-ss")
		val outputDir = Paths.get(outputFileName, sdf.format(new Date))

		val latencyFile = outputDir.resolve("proc" + processId + ".csv")
		val runtimeFile = outputDir.resolve("runtime" + processId + ".csv")

		//Initialize files
		try {
			Files.createDirectories(outputDir)

			Files.deleteIfExists(latencyFile)
			Files.createFile(latencyFile)

			Files.deleteIfExists(runtimeFile)
			Files.createFile(runtimeFile)
		} catch {
			case e : IOException =>
				throw new IllegalStateException("cannot instantiate output file", e)
		}

		val latencyWriter = new PrintWriter(latencyFile.toFile)
		val runtimeWriter = new PrintWriter(runtimeFile.toFile)

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
		} finally {
			latencyWriter.close()
			runtimeWriter.close()
		}

		//Wait for measurement being done.
		system.barrier("measure-done")
		println("## MEASUREMENT DONE ##")
	}

	private def doOperations(): Unit = {

	}


	def runBenchmark() : Unit = JReplicaSystems.withActorSystem(
		address,
		JavaConverters.asJavaIterable(replicas),
		java.time.Duration.ofSeconds(30000)
	).use( () => { warmup(); measure() } )
}

object DistributedBenchmark {

	final val BARRIER_TIMEOUT : Duration = Duration(1800, "s")

	case class BenchmarkCommunication()

	def start(benchmark : Class[_ <: DistributedBenchmark], configName : String) : Unit = {


		val constructor = benchmark.getConstructor(classOf[Config])
		val bench = constructor.newInstance(ConfigFactory.load(configName))

		bench.runBenchmark()

	}

}
