package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.legacy.DistributedBenchmark;
import de.tuda.stg.consys.bench.OutputResolver;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import scala.concurrent.duration.Duration;

import java.util.*;
import java.util.function.Supplier;

/**
 * Created on 19.11.19.
 *
 * @author Mirko Köhler
 */
@Deprecated
public abstract class CassandraDemoBenchmark extends DistributedBenchmark<CassandraStoreBinding> {

	protected enum BenchmarkType {
		WEAK, MIXED, STRONG, OP_MIXED
	}

	private final BenchmarkType benchType;
	protected boolean isTestMode = false;
	private static final int msTimeout = 60000;
	// utility for benchmarks
	protected final Random random = new Random();


	public CassandraDemoBenchmark(String name, Config config, Option<OutputResolver> outputResolver) {
		super(name, config, outputResolver, (address, processId, barrier) -> {
			CassandraStoreBinding store = null;

			if ((int)processId == 0) {
				store = CassandraReplica.create(address.hostname(), address.port1(), address.port2(),
						Duration.apply(msTimeout, "ms"), true);
			}

			try {
				barrier.barrier("init-store");
			} catch (Exception e) {
				throw new RuntimeException("error executing barrier during store construction in process " + processId +
						". Reason: " + e.getMessage());
			}

			if ((int)processId != 0) {
				store = CassandraReplica.create(address.hostname(), address.port1(), address.port2(),
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

	public CassandraDemoBenchmark(Config config, Option<OutputResolver> outputResolver) {
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

	protected BenchmarkType getBenchType() {
		return benchType;
	}

	void enableTestMode() {
		this.isTestMode = true;
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

	protected List<Double> zipfSummed(int n, double s) {
		double e = 0;
		for (int i = 1; i < n + 1; i++) {
			e += 1 / Math.pow(i, s);
		}

		List<Double> result = new ArrayList<>(n);
		for (int k = 1; k < n + 1; k++) {
			double z = (1 / Math.pow(k, s)) / e;
			double sum = result.isEmpty() ? z : result.get(result.size() - 1) + z;
			result.add(sum);
		}

		return result;
	}

	protected List<Double> zipfSummed(int n) {
		return zipfSummed(n, 1);
	}

	protected void randomTransaction(List<Runnable> operations, List<Double> zipf) {
		float rand = random.nextFloat();

		for (int i = 0; i < zipf.size(); i++) {
			if (rand < zipf.get(i)) {
				operations.get(i).run();
				return;
			}
		}
		// in case of rounding errors
		operations.get(operations.size() - 1).run();
	}

	// Utility method for benchmarks
	protected <E> E getRandomElement(List<E> list) {
		return list.get(random.nextInt(list.size()));
	}

	// Utility method for benchmarks
	protected <E> E getRandomElementExcept(List<E> list, E object) {
		E element;
		do {
			element = list.get(random.nextInt(list.size()));
		} while (element == object);
		return element;
	}

	protected String generateRandomText(int nWords, List<String> words) {
		StringBuilder body = new StringBuilder(words.get(random.nextInt(words.size())));
		for (int i = 0; i < nWords - 1; i++)
			body.append(" ").append(words.get(random.nextInt(words.size())));
		return body.toString();
	}

	public void test() {}

	private final Map<String, List<Boolean>> checkResults = new HashMap<>();
	private final Map<String, List<String>> checkResultsMessage = new HashMap<>();

	public void check(String name, Supplier<Boolean> code) {
		putCheck(name, code.get());
	}

	public void check(String name, boolean result) {
		putCheck(name, result);
	}

	public <T> void checkEquals(String name, T expected, T actual) {
		boolean result = expected.equals(actual);
		putCheck(name, result);
		if (!result) {
			checkResultsMessage.putIfAbsent(name, new ArrayList<>());
			checkResultsMessage.get(name).add("expected: " + expected + ", but actual: " + actual);
		}
	}

	public void checkFloatEquals(String name, float expected, float actual) {
		checkFloatEquals(name, expected, actual, 0.000001f);
	}
	public void checkFloatEquals(String name, float expected, float actual, float eps) {
		boolean result = Math.abs(expected - actual) < eps;
		putCheck(name, result);
		if (!result) {
			checkResultsMessage.putIfAbsent(name, new ArrayList<>());
			checkResultsMessage.get(name).add("expected: " + expected + ", but actual: " + actual);
		}
	}

	private void putCheck(String name, boolean result) {
		checkResults.putIfAbsent(name, new ArrayList<>());
		checkResults.get(name).add(result);
	}

	public void printTestResult() {
		if (processId() != 0) return;

		long nFailedChecks = checkResults.values().stream().flatMap(Collection::stream).filter(b -> !b).count();

		System.out.println("- TEST RESULTS ---------");
		System.out.println("Failed checks (" + nFailedChecks + "/" + checkResults.values().stream().mapToLong(Collection::size).sum() + "):");
		for (var pair : checkResults.entrySet()) {
			nFailedChecks = pair.getValue().stream().filter(b -> !b).count();
			if (nFailedChecks > 0) {
				System.out.println("  " + pair.getKey() + " (failed " + nFailedChecks + "/" + pair.getValue().size() + ")");
				if (checkResultsMessage.containsKey(pair.getKey())) {
					for (String msg : checkResultsMessage.get(pair.getKey()))
						System.out.println("     " + msg);
				}
			}
		}
		System.out.println("------------------------");
	}
}
