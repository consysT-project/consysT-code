package de.tuda.stg.consys.demo.crdts;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.BaseStoreBenchmark;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.bench.StoreBenchmark;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.demo.JStoreBenchmark;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.demo.crdts.schema.GCounter;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import scala.Option;

import java.util.Random;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class CRDTBenchmark extends JStoreBenchmark<AkkaStore> {

	@Override
	protected Store createJStore(BaseStoreBenchmark<AkkaStore> benchmark) {
		return null;
	}

	public CRDTBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
		super(config, outputResolver);
	}

	private final Random random = new Random();
	private Ref<GCounter> counter;

	@Override
	public void setup() {
		if (processId() == 0) {
			var tx = store().transaction(ctx -> {
				var ref = ctx.replicate("de/tuda/stg/consys/demo/crdts", getWeakLevel(), Counter.class, 0);
				return ref;
			});

			counter =
		}
		barrier("counter_added");
		if (processId() != 0) {
			counter = store().transaction(ctx -> Option.apply(ctx.lookup("de/tuda/stg/consys/demo/crdts", getWeakLevel(), Counter.class))).get();
		}
	}

	@Override
	public void operation() {
		int roll = random.nextInt(100);
		store().transaction(ctx -> {
			if (roll < 50) {
				counter.ref().inc();
			} else {
				counter.ref().get();
			}
			return Option.empty();
		});
		System.out.print(".");
	}

	@Override
	public void cleanup() {
		super.cleanup();
	}


}
