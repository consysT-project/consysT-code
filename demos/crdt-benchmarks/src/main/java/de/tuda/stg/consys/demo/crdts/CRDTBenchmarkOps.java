package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.StoreBenchmarkConfig;
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
public class CRDTBenchmarkOps extends JBenchOperation {

	private final Random random = new Random();
	private Ref<GCounter> counter;

	protected CRDTBenchmarkOps(JBenchStore adapter, StoreBenchmarkConfig config) {
		super(adapter, config);
	}


	@Override
	public void setup() {
		if (processId() == 0) {
			store().transaction(ctx -> {
				counter = ctx.replicate("counter", getWeakLevel(), GCounter.class, 0);
				return Option.apply(42);
			});
		}
		barrier("counter_added");
		if (processId() != 0) {
			store().transaction(ctx -> {
				counter = ctx.lookup("counter", getWeakLevel(), GCounter.class);
				return Option.apply(42);
			});
		}
	}

	@Override
	public void operation() {
		int roll = random.nextInt(100);
		store().transaction(ctx -> {
			if (roll < 50) {
				counter.ref().inc();
			} else {
				counter.ref().getValue();
			}
			return Option.empty();
		});
		System.out.print(".");
	}

	@Override
	public void cleanup() {

	}


}
