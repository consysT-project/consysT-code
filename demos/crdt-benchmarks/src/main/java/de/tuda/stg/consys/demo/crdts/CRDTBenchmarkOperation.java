package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.JBenchOperation;
import de.tuda.stg.consys.demo.crdts.schema.GCounter;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

import java.util.Random;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class CRDTBenchmarkOperation extends JBenchOperation {

	public CRDTBenchmarkOperation(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config);
	}

	private final Random random = new Random();
	private Ref<GCounter> counter;

	@Override
	public void setup() {
		if (processId() == 0) {
			Option<Ref<GCounter>> result = store().transaction(ctx -> {
				var ref = ctx.replicate("counter", getWeakLevel(), GCounter.class);
				return Option.apply(ref);
			});
			counter = result.get();
		}
		barrier("counter_added");
		if (processId() != 0) {
			Option<Ref<GCounter>> result = store().transaction(ctx -> {
				var ref = ctx.lookup("counter", getWeakLevel(), GCounter.class);
				return Option.apply(ref);
			});
			counter = result.get();
		}
	}

	@Override
	public void operation() {
		int roll = random.nextInt(100);
		store().transaction(ctx -> {
			if (roll < 50) {
				counter.invoke("inc");
			} else {
				counter.invoke("getValue");
			}
			return Option.empty();
		});
		System.out.print(".");
	}

	@Override
	public void cleanup() {

	}


}
