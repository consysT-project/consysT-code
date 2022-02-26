package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.DistributedBenchmark;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

import java.util.Random;

import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import scala.concurrent.duration.Duration;

/**
 * Created on 19.11.19.
 *
 * @author Mirko Köhler
 */
public abstract class CassandraDemoBenchmark extends DistributedBenchmark<CassandraStoreBinding> {

	private enum BenchmarkType {
		WEAK, MIXED, STRONG, OP_MIXED
	}

	private final BenchmarkType benchType;


	// An executor to use for asynchronous syncs.
	//private ExecutorService executor = Executors.newCachedThreadPool(); //Currently unused
	private final Random random = new Random();


	public CassandraDemoBenchmark(String name, Config config, Option<OutputFileResolver> outputResolver) {
		super(name, config, outputResolver, (address, processId) ->
			Cassandra.newReplica(address.hostname(), address.port1(), address.port2(),
					Duration.apply(50, "ms"), (int)processId == 0));

		String typeString = config.getString("consys.bench.demo.type");
		if (typeString == null) {
			throw new IllegalArgumentException("config key not found: consys.bench.demo.type");
		}
		benchType = BenchmarkType.valueOf(typeString.toUpperCase());
	}

	public CassandraDemoBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
		this("default", config, outputResolver);
	}

	protected void doSync(Runnable f)  {
//		final JAkkaReplicaSystem sys = system();
//		executor.execute(JReplicaSystems.withSystem(sys).use(() -> f));
		if (shouldSync()) f.run();
	}

	protected boolean shouldSync() {
		return random.nextInt(100) < 20;
	}

	protected ConsistencyLevel<CassandraStore> getStrongLevel() {
		switch (benchType) {
			case WEAK: return CassandraConsistencyLevels.WEAK;
			case OP_MIXED: return CassandraConsistencyLevels.MIXED;
			default: return CassandraConsistencyLevels.STRONG;
		}
	}

	protected ConsistencyLevel<CassandraStore> getWeakLevel() {
		switch (benchType) {
			case STRONG: return CassandraConsistencyLevels.STRONG;
			case OP_MIXED: return CassandraConsistencyLevels.MIXED;
			default: return CassandraConsistencyLevels.WEAK;
		}
	}

/*
	protected ConsistencyLabel getCausalLevel() {
		switch (benchType) {
			case MIXED: return JConsistencyLevels.CAUSAL;
			case STRONG: return JConsistencyLevels.STRONG;
			case WEAK: return JConsistencyLevels.WEAK;
		}

		throw new IllegalArgumentException("unsupported benchtype " + benchType);
	}
*/

	@Override
	public void closeOperations() {
		/*
		try {
			executor.shutdown();
			executor.awaitTermination(5, TimeUnit.MINUTES);
			executor = Executors.newCachedThreadPool();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		*/
	}
}
