package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.JBenchRunnable;
import de.tuda.stg.consys.demo.crdts.schema.GCounter;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.utils.Logger;
import scala.Option;

import java.util.Random;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class CRDTBenchmarkRunnable extends JBenchRunnable {

	public CRDTBenchmarkRunnable(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config);
	}

	private Ref<GCounter> counter;

	@Override
	public void setup() {
		if (processId() == 0) {
			Option<Ref<GCounter>> result = store().transaction(ctx -> {
				var ref = ctx.replicate("counter", getStrongLevel(), GCounter.class);
				return Option.apply(ref);
			});
			counter = result.get();
		}
		barrier("counter_added");
		if (processId() != 0) {
			Option<Ref<GCounter>> result = store().transaction(ctx -> {
				var ref = ctx.lookup("counter", getStrongLevel(), GCounter.class);
				return Option.apply(ref);
			});
			counter = result.get();
		}
		barrier("counter_lookup");
	}

	@Override
	public BenchmarkOperations operations() {
		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
							counter.invoke("inc");
							return Option.apply(0);
						}),
				() -> store().transaction(ctx -> {
					counter.invoke("inc");
					return Option.apply(0);
				})
		});
	}

	@Override
	public void cleanup() {

		store().transaction(ctx -> {
			var result = counter.invoke("getValue");
			Logger.info(result);
			return Option.apply(0);
		});
	}


}
