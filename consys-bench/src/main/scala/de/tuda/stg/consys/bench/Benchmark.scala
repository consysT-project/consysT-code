package de.tuda.stg.consys.bench

/**
 * Created on 29.10.19.
 *
 * @author Mirko Köhler
 */
import com.typesafe.config.Config
import com.typesafe.config.ConfigFactory
import de.tuda.stg.consys.checker.qual.Strong
import de.tuda.stg.consys.objects.japi.{JConsistencyLevels, JRef, JReplicaSystem, JReplicaSystems}
import java.io.FileNotFoundException
import java.io.IOException
import java.io.PrintWriter
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.text.SimpleDateFormat
import java.util.Date

import de.tuda.stg.consys.bench.Benchmark.BenchmarkCommunication

import scala.concurrent.duration.Duration


/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
abstract class Benchmark(
	val address : Address,
	val replicas : Array[Address],
	var processId : Int /* process 0 is the coordinator */ ,
	val warmupIterations : Int,
	val measureIterations : Int,
	val outputFileName : String
) {
	//Important: create the followers before creating the coordinator
	final protected var replicaSystem : JReplicaSystem = JReplicaSystems.fromActorSystem(
		address.hostname,
		address.port,
		java.time.Duration.ofSeconds(600)
	)

		for (replica <- replicas) {
		replicaSystem.addReplicaSystem(replica.hostname, replica.port)
	}

	println("Waiting for other replicas...")
	Thread.sleep(60000)

	final private var commChannel : JRef[BenchmarkCommunication] = _

	if (processId == 0) { //The coordinator creates a new communication channel
		commChannel = replicaSystem.replicate("$communication", BenchmarkCommunication(), JConsistencyLevels.STRONG)
	}
	else { //The followers wait until the communication channel has been created
		commChannel = replicaSystem.lookup("$communication", classOf[BenchmarkCommunication], JConsistencyLevels.STRONG)
		commChannel.await()
	}


	def this(config : Config) {
		this(
			Address.create(config.getString("consys.bench.hostname")),
			config.getStringList("consys.bench.otherReplicas").stream().map[Address](str => Address.create(str)).toArray(i => new Array[Address](i)),
			config.getInt("consys.bench.processId"),
			config.getInt("consys.bench.warmupIterations"),
			config.getInt("consys.bench.measureIterations"),
			config.getString("consys.bench.outputFile")
		)
	}


	def this(configName : String) {
		this(ConfigFactory.load(configName))
	}



	protected def setup() : Unit

	protected def iteration() : Unit

	protected def cleanup() : Unit




	private def warmup() : Unit = {
		println("## START WARMUP ##")
		replicaSystem.barrier("warmup")
		for (_ <- 0 to warmupIterations) {
			println("### SETUP ###")
			replicaSystem.barrier("setup")
			setup()
			Thread.sleep(2000)
			println("### ITERATIONS ###")
			replicaSystem.barrier("iterations")
			iteration()
			Thread.sleep(2000)
			println("### CLEANUP ###")
			replicaSystem.barrier("cleanup")
			cleanup()
			Thread.sleep(2000)
		}
		println("## WARMUP DONE ##")
		replicaSystem.barrier("warmup-done")
	}


	private def measure() : Unit = {
		println("## START MEASUREMENT ##")
		replicaSystem.barrier("measure")
		val sdf = new SimpleDateFormat("YY-MM-dd kk:mm:ss")
		val outputDir = Paths.get(outputFileName, sdf.format(new Date))
		val outputFile = outputDir.resolve("proc" + processId + ".csv")

		try {
			Files.createDirectories(outputDir)
			Files.deleteIfExists(outputFile)
			Files.createFile(outputFile)
		} catch {
			case e : IOException =>
				throw new IllegalStateException("cannot instantiate output file", e)
		}

		val writer = new PrintWriter(outputFile.toFile)
		try {
			writer.println("iteration,ns")
			for (i <- 0 to measureIterations) {
				println("### SETUP ###")
				replicaSystem.barrier("setup")
				setup()
				Thread.sleep(2000)
				println("### ITERATIONS ###")
				replicaSystem.barrier("iterations")
				val start = System.nanoTime
				iteration()
				val duration = System.nanoTime - start
				writer.println("" + i + "," + duration)
				Thread.sleep(2000)
				println("### CLEANUP ###")
				replicaSystem.barrier("cleanup")
				cleanup()
				Thread.sleep(2000)
			}
		} catch {
			case e : FileNotFoundException =>
				throw new IllegalStateException("file not found: " + outputFile, e)
		} finally {
			writer.close()
		}

		println("## MEASUREMENT DONE ##")
		replicaSystem.barrier("measure-done")
	}


	def runBenchmark() : Unit = {
		warmup()
		measure()
		replicaSystem.close()
	}
}

object Benchmark {

	final val BARRIER_TIMEOUT : Duration = Duration(600, "s")

	case class BenchmarkCommunication()

	def start(benchmark : Class[_ <: Benchmark], configName : String) : Unit = {

		val constructor = benchmark.getConstructor(classOf[Config])
		val bench = constructor.newInstance(ConfigFactory.load(configName))

		bench.runBenchmark()

	}

}
