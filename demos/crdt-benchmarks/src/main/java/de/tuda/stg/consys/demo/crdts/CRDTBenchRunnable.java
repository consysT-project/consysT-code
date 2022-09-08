package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.JBenchRunnable;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.logging.Logger;
import scala.Option;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public abstract class CRDTBenchRunnable<CRDT> extends JBenchRunnable {

	private final Class<CRDT> clazz;

	protected Ref<CRDT> crdt = null;


	public CRDTBenchRunnable(JBenchStore adapter, BenchmarkConfig config, Class<CRDT> clazz) {
		super(adapter, config);
		this.clazz = clazz;

		Logger.info("Created benchmark for " + clazz.getSimpleName());
	}



	@Override
	public void setup() {
		if (processId() == 0) {
			Option<Ref<CRDT>> result = store().transaction(ctx -> {
				var ref = ctx.replicate("crdt", getWeakLevel(), clazz);
				return Option.apply(ref);
			});

			crdt = result.get();
		}

		barrier("crdt-added");

		if (processId() != 0) {
			Option<Ref<CRDT>> result = store().transaction(ctx -> {
				var ref = ctx.lookup("crdt", getWeakLevel(), clazz);
				return Option.apply(ref);
			});

			crdt = result.get();
		}

		barrier("crdt-lookup");
	}

	@Override
	public void cleanup() { }

	@Override
	public void closeOperations() {
		super.closeOperations();
	}


}
