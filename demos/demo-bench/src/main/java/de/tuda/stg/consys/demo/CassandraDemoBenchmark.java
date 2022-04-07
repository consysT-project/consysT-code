package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.DistributedBenchmark;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import scala.concurrent.duration.Duration;

import java.lang.reflect.InvocationTargetException;

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
	private static final int msTimeout = 60000;


	public CassandraDemoBenchmark(String name, Config config, Option<OutputFileResolver> outputResolver) {
		super(name, config, outputResolver, (address, processId, barrier) -> {
			CassandraStoreBinding store = null;

			if ((int)processId == 0) {
				store = Cassandra.newReplica(address.hostname(), address.port1(), address.port2(),
						Duration.apply(msTimeout, "ms"), true);
			}

			try {
				barrier.barrier("init-store");
			} catch (Exception e) {
				e.printStackTrace();
				throw new RuntimeException("error executing barrier during store construction");
			}

			if ((int)processId != 0) {
				store = Cassandra.newReplica(address.hostname(), address.port1(), address.port2(),
						Duration.apply(msTimeout, "ms"), false);
			}

			return store;
		});

		String typeString = config.getString("consys.bench.demo.type");
		if (typeString == null) {
			throw new IllegalArgumentException("config key not found: consys.bench.demo.type");
		}
		benchType = BenchmarkType.valueOf(typeString.toUpperCase());
	}

	public CassandraDemoBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
		this("default", config, outputResolver);
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

	@Override
	public void setup() {
		if (store() == null) {
			store_$eq(storeCreator().apply(address(), processId(), system()));
		}
	}

	@Override
	public void cleanup() {
		try {
			store().close();
			store_$eq(null);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("error cleaning up store");
		}
	}

	protected void barrier(String name) {
		try {
			system().barrier(name);
		} catch (Exception e) {
			e.printStackTrace();
			throw new RuntimeException("Error executing barrier '" + name + "'");
		}
	}

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
