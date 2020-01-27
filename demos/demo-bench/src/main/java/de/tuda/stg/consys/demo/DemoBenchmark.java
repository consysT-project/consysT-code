package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.DistributedBenchmark;
import de.tuda.stg.consys.core.ConsistencyLabel;
import de.tuda.stg.consys.japi.JConsistencyLevels;

/**
 * Created on 19.11.19.
 *
 * @author Mirko Köhler
 */
public abstract class DemoBenchmark extends DistributedBenchmark {

	private enum BenchmarkType {
		MIXED, STRONG
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

	protected ConsistencyLabel getStrongLevel() {
		return JConsistencyLevels.STRONG;
	}

	protected ConsistencyLabel getWeakLevel() {
		switch (benchType) {
			case MIXED: return JConsistencyLevels.WEAK;
			case STRONG: return JConsistencyLevels.STRONG;
		}

		throw new IllegalArgumentException("unsupported benchtype " + benchType);
	}

	protected ConsistencyLabel getCausalLevel() {
		switch (benchType) {
			case MIXED: return JConsistencyLevels.CAUSAL;
			case STRONG: return JConsistencyLevels.STRONG;
		}

		throw new IllegalArgumentException("unsupported benchtype " + benchType);
	}
}
