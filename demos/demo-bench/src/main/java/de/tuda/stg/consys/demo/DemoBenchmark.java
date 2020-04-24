package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.DistributedBenchmark;
import de.tuda.stg.consys.core.ConsistencyLevel;
import de.tuda.stg.consys.japi.JConsistencyLevels;

import static de.tuda.stg.consys.japi.JConsistencyLevels.WEAK;

/**
 * Created on 19.11.19.
 *
 * @author Mirko Köhler
 */
public abstract class DemoBenchmark extends DistributedBenchmark {

	private enum BenchmarkType {
		WEAK, MIXED, STRONG
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
		switch (benchType) {
			case WEAK: return WEAK;
			default: return JConsistencyLevels.STRONG;
		}


	}

	protected ConsistencyLevel getWeakLevel() {
		switch (benchType) {
			case STRONG: return JConsistencyLevels.STRONG;
			default: return JConsistencyLevels.WEAK;
		}

	}

	protected ConsistencyLevel getCausalLevel() {
		switch (benchType) {
			case MIXED: return JConsistencyLevels.CAUSAL;
			case STRONG: return JConsistencyLevels.STRONG;
			case WEAK: return JConsistencyLevels.WEAK;
		}

		throw new IllegalArgumentException("unsupported benchtype " + benchType);
	}
}
