package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.DistributedBenchmark;
import de.tuda.stg.consys.objects.ConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;

/**
 * Created on 19.11.19.
 *
 * @author Mirko Köhler
 */
public abstract class DemoBenchmark extends DistributedBenchmark {

	private enum BenchmarkType {
		MIXED, STRONG;
	}


	private final BenchmarkType benchType;


	public DemoBenchmark(Config config) {
		super(config);

		String typeString = config.getString("consys.bench.demo.type");

		if (typeString == null) {
			throw new IllegalArgumentException("config key not found: consys.bench.demo.type");
		}

		benchType = BenchmarkType.valueOf(typeString.toUpperCase());
	}

	protected ConsistencyLevel getStrongLevel() {
		return JConsistencyLevels.STRONG;
	}

	protected ConsistencyLevel getWeakLevel() {
		switch (benchType) {
			case MIXED: return JConsistencyLevels.WEAK;
			case STRONG: return JConsistencyLevels.STRONG;
		}

		throw new IllegalArgumentException("unsupported benchtype " + benchType);
	}

	protected ConsistencyLevel getCausalLevel() {
		switch (benchType) {
			case MIXED: return JConsistencyLevels.CAUSAL;
			case STRONG: return JConsistencyLevels.STRONG;
		}

		throw new IllegalArgumentException("unsupported benchtype " + benchType);
	}
}
