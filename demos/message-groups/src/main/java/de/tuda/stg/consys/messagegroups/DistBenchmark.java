package de.tuda.stg.consys.messagegroups;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.nio.file.Paths;

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

		if (processId == 0) {
			//The coordinator creates a new communication channel
			commChannel = replicaSystem.replicate("$communication", new BenchmarkCommunication(), JConsistencyLevel.STRONG);
		} else {
			//The followers wait until the communication channel has been created
			commChannel = replicaSystem.lookup("$communication", BenchmarkCommunication.class, JConsistencyLevel.STRONG);
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
		for (int i = 0; i < warmupIterations; i++) {
			setup();
			iteration();
			cleanup();
		}
	}

	private void measure() {
		try (PrintWriter writer = new PrintWriter(Paths.get(outputFileName, "proc" + processId + ".csv").toFile())) {
			for (int i = 0; i < measureIterations; i++) {
				setup();
				long start = System.nanoTime();
				iteration();
				long duration = System.nanoTime() - start;
				writer.println("" + i + "," + duration);
				cleanup();
			}
		} catch (FileNotFoundException e) {
			throw new IllegalStateException("cannot instantiate output file");
		}
	}

	public void runBenchmark() {
		warmup();
		measure();
	}










}
