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

import de.tuda.stg.consys.bench.DistributedBenchmark.BenchmarkCommunication

import scala.concurrent.duration.Duration


/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
abstract class DistributedBenchmark(
	val address : Address,
	val replicas : Array[Address],
	var processId : Int /* process 0 is the coordinator */ ,
	val warmupIterations : Int,
	val measureIterations : Int,
	var stepsPerIteration : Int,
	var waitBetweenOperations : Int,
	val outputFileName : String
) {
	//Important: create the followers before creating the coordinator
	final protected var replicaSystem : JReplicaSystem = JReplicaSystems.fromActorSystem(
		address.hostname,
		address.port,
		java.time.Duration.ofSeconds(30000)
	)

	println("Adding other replicas...")
	for (replica <- replicas) {
		replicaSystem.addReplicaSystem(replica.hostname, replica.port)
	}
	println("All replicas found")




//	final private var commChannel : JRef[BenchmarkCommunication] = _
//
//	if (processId == 0) { //The coordinator creates a new communication channel
//		commChannel = replicaSystem.replicate("$communication", BenchmarkCommunication(), JConsistencyLevels.STRONG)
//	}
//	else { //The followers wait until the communication channel has been created
//		commChannel = replicaSystem.lookup("$communication", classOf[BenchmarkCommunication], JConsistencyLevels.STRONG)
//		commChannel.await()
//	}


	def this(config : Config) {
		this(
			Address.create(config.getString("consys.bench.hostname")),
			config.getStringList("consys.bench.otherReplicas").stream().map[Address](str => Address.create(str)).toArray(i => new Array[Address](i)),
			config.getInt("consys.bench.processId"),
			config.getInt("consys.bench.warmupIterations"),
			config.getInt("consys.bench.measureIterations"),
			1,
			0,
			config.getString("consys.bench.outputFile")
		)
	}


	def this(configName : String) {
		this(ConfigFactory.load(configName))
	}



	protected def setup() : Unit

	protected def iteration() : Unit

	protected def cleanup() : Unit


	protected def setStepsPerIteration(steps : Int) : Unit = {
		stepsPerIteration = steps;
	}

	protected def setWaitPerIteration(ms : Int) : Unit = {
		waitBetweenOperations = ms;
	}

	private def busyWait(ms : Int) : Unit = {
		val start = System.currentTimeMillis
		while (System.currentTimeMillis < start + ms) {}
	}


	private def warmup() : Unit = {
		replicaSystem.barrier("warmup")
		println("## START WARMUP ##")
		for (i <- 0 to warmupIterations) {
			replicaSystem.barrier("setup")
			println(s"### SETUP : WARMUP $i ###")
			setup()
			replicaSystem.barrier("iterations")
			println(s"### ITERATIONS : WARMUP $i ###")
			for (i <- 1 to stepsPerIteration) iteration()
			replicaSystem.barrier("cleanup")
			println(s"### CLEANUP : WARMUP $i ###")
			cleanup()
		}
		replicaSystem.barrier("warmup-done")
		println("## WARMUP DONE ##")
	}


	private def measure() : Unit = {
		replicaSystem.barrier("measure")
		println("## START MEASUREMENT ##")
		val sdf = new SimpleDateFormat("YY-MM-dd_kk-mm-ss")
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
				replicaSystem.barrier("setup")
				println(s"### SETUP : MEASURE $i ###")
				setup()
				replicaSystem.barrier("iterations")
				println(s"### ITERATIONS : MEASURE $i ###")
				for (i <- 1 to stepsPerIteration) {
					if (waitBetweenOperations != 0) busyWait(waitBetweenOperations)
					val start = System.nanoTime
					iteration()
					val duration = System.nanoTime - start
					writer.println("" + i + "," + duration)
				}
				writer.flush()
				replicaSystem.barrier("cleanup")
				println(s"### CLEANUP : MEASURE $i ###")
				cleanup()
			}
		} catch {
			case e : FileNotFoundException =>
				throw new IllegalStateException("file not found: " + outputFile, e)
		} finally {
			writer.close()
		}
		replicaSystem.barrier("measure-done")
		println("## MEASUREMENT DONE ##")
	}


	def runBenchmark() : Unit = {
		warmup()
		measure()
		replicaSystem.close()
	}
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
