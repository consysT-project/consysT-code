package de.tuda.stg.consys.bench;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.SimpleDateFormat;
import java.util.Date;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
abstract public class DistBenchmark {

//	public static void main(String[] args) {
//		DistBenchmark bench = new DistBenchmark(ConfigFactory.load(args[0]));
//	}

	protected final Address[] replicas;

	protected final JReplicaSystem replicaSystem;

	private final JRef<@Strong BenchmarkCommunication> commChannel;

	protected final int processId; /* process 0 is the coordinator */

	private final int warmupIterations;
	private final int measureIterations;

	private final String outputFileName;

	//Important: create the followers before creating the coordinator
	public DistBenchmark(Address address, Address[] replicas, int processId, int warmupIterations, int measureIterations, String outputFileName) {
		this.replicas = replicas;
		this.processId = processId;
		this.warmupIterations = warmupIterations;
		this.measureIterations = measureIterations;
		this.outputFileName = outputFileName;

		replicaSystem = JReplicaSystem.fromActorSystem(address.getHostname(), address.getPort());
		for (Address replica : replicas) {
			replicaSystem.addReplicaSystem(replica.getHostname(), replica.getPort());
		}

		try {
			Thread.sleep(10000);
		} catch (InterruptedException e) {
			e.printStackTrace();
		}

		if (processId == 0) {
			//The coordinator creates a new communication channel
			commChannel = replicaSystem.replicate("$communication", new BenchmarkCommunication(), JConsistencyLevels.STRONG);
		} else {
			//The followers wait until the communication channel has been created
			commChannel = replicaSystem.lookup("$communication", BenchmarkCommunication.class, JConsistencyLevels.STRONG);
			commChannel.await();
		}
	}

	public DistBenchmark(Config config) {
		this(
			new Address(config.getString("consys.bench.hostname")),
			config.getStringList("consys.bench.otherReplicas").stream()
				.map(Address::new).toArray(Address[]::new),
			config.getInt("consys.bench.processId"),
			config.getInt("consys.bench.warmupIterations"),
			config.getInt("consys.bench.measureIterations"),
			config.getString("consys.bench.outputFile")
		);
	}

	public DistBenchmark(String configName) {
		this(ConfigFactory.load(configName));
	}

	abstract protected void setup();

	abstract protected void iteration();

	abstract protected void cleanup();




	private void warmup() {
		System.out.println("## START WARMUP ##");
		replicaSystem.barrier("warmup");

		for (int i = 0; i < warmupIterations; i++) {
			System.out.println("### SETUP ###");
			replicaSystem.barrier("setup");
			setup();
			System.out.println("### ITERATIONS ###");
			replicaSystem.barrier("iterations");
			iteration();
			System.out.println("### CLEANUP ###");
			replicaSystem.barrier("cleanup");
			cleanup();
		}

		System.out.println("## WARMUP DONE ##");
		replicaSystem.barrier("warmup-done");
	}

	private void measure() {
		System.out.println("## START MEASUREMENT ##");
		replicaSystem.barrier("measure");

		SimpleDateFormat sdf = new SimpleDateFormat("YY-MM-dd kk:mm:ss");
		Path outputDir = Paths.get(outputFileName, sdf.format(new Date()));
		Path outputFile =  outputDir.resolve("proc" + processId + ".csv");
		try {
			Files.createDirectories(outputDir);
			Files.deleteIfExists(outputFile);
			Files.createFile(outputFile);
		} catch (IOException e) {
			throw new IllegalStateException("cannot instantiate output file", e);
		}

		try (PrintWriter writer = new PrintWriter(outputFile.toFile())) {
			writer.println("iteration,ns");
			for (int i = 0; i < measureIterations; i++) {
				System.out.println("### SETUP ###");
				replicaSystem.barrier("setup");
				setup();
				System.out.println("### ITERATIONS ###");
				replicaSystem.barrier("iterations");
				long start = System.nanoTime();
				iteration();
				long duration = System.nanoTime() - start;
				writer.println("" + i + "," + duration);
				System.out.println("### CLEANUP ###");
				replicaSystem.barrier("cleanup");
				cleanup();
			}
		} catch (FileNotFoundException e) {
			throw new IllegalStateException("file not found: " + outputFile, e);
		}

		System.out.println("## MEASUREMENT DONE ##");
		replicaSystem.barrier("measure-done");
	}

	public void runBenchmark() {
		warmup();
		measure();

		try {
			replicaSystem.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}










}
