package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.JBenchRunnable;
import de.tuda.stg.consys.invariants.utils.InvariantUtils;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.logging.Logger;
import scala.Option;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public abstract class CRDTBenchRunnable<CRDT> extends DemoRunnable {

	private final Class<CRDT> clazz;

	protected Ref<CRDT> crdt = null;


	public CRDTBenchRunnable(JBenchStore adapter, BenchmarkConfig config, Class<CRDT> clazz) {
		super(adapter, config);
		this.clazz = clazz;

		String typeString = config.toConfig().getString("consys.bench.demo.type");
		if (typeString == null) {
			throw new IllegalArgumentException("config key not found: consys.bench.demo.type");
		}

		InvariantUtils.setReplicaId(config.processId());
		InvariantUtils.setNumOfReplicas(config.numberOfReplicas());

		Logger.info("Created benchmark for " + clazz.getSimpleName());
	}



	@Override
	public void setup() {
		if (processId() == 0) {
			Option<Ref<CRDT>> result = store().transaction(ctx -> {
				var ref = ctx.replicate("crdt", getLevelWithMixedFallback(getMixedLevel()), clazz);
				return Option.apply(ref);
			});

			crdt = result.get();
		}

		try {
			Thread.sleep(5000);
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		}

		barrier("crdt-added");

		if (processId() != 0) {
			Option<Ref<CRDT>> result = store().transaction(ctx -> {
				var ref = ctx.lookup("crdt", getLevelWithMixedFallback(getMixedLevel()), clazz);
				return Option.apply(ref);
			});

			crdt = result.get();
		}

		try {
			Thread.sleep(5000);
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		}



		barrier("crdt-lookup");
	}



	@Override
	public void cleanup() {
		try {
			Thread.sleep(5000);
		} catch (InterruptedException e) {
			throw new RuntimeException(e);
		}
	}

	@Override
	public void closeOperations() {
		super.closeOperations();
	}


}
