package de.tuda.stg.consys.messagegroups;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.FileNotFoundException;
import java.io.PrintWriter;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
abstract public class DistBenchmark {

	public static void main(String[] args) {

	}

	protected final String[] replicas;

	private final JReplicaSystem replicaSystem;

	private final JRef<@Strong BenchmarkCommunication> commChannel;

	protected final boolean isCoordinator;

	private final int warmupIterations;
	private final int measureIterations;

	private final String outputFileName;

	//Important: create the followers before creating the coordinator
	public DistBenchmark(String hostname, int port, String[] replicas, boolean isCoordinator, int warmupIterations, int measureIterations, String outputFileName) {
		this.replicas = replicas;
		this.isCoordinator = isCoordinator;
		this.warmupIterations = warmupIterations;
		this.measureIterations = measureIterations;
		this.outputFileName = outputFileName;

		replicaSystem = JReplicaSystem.fromActorSystem(hostname, port);
		for (String replica : replicas) {
			String[] hostnameAndPort = replica.split(":");
			replicaSystem.addReplicaSystem(hostnameAndPort[0], Integer.parseInt(hostnameAndPort[1]));
		}

		if (isCoordinator) {
			//The coordinator creates a new communication channel
			commChannel = replicaSystem.replicate("$communication", new BenchmarkCommunication(), JConsistencyLevel.STRONG);
		} else {
			//The followers wait until the communication channel has been created
			commChannel = replicaSystem.ref("$communication", BenchmarkCommunication.class, JConsistencyLevel.STRONG);
			commChannel.await();
		}

	}

	abstract public void iteration();


	private void warmup() {
		for (int i = 0; i < warmupIterations; i++) {
			iteration();
		}
	}

	private void measure() {
		try (PrintWriter writer = new PrintWriter(outputFileName)) {
			for (int i = 0; i < measureIterations; i++) {
				long start = System.nanoTime();
				iteration();
				long duration = System.nanoTime() - start;
				writer.println("" + i + "," + duration);
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
