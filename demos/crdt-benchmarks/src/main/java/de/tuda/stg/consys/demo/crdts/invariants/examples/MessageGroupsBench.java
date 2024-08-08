package de.tuda.stg.consys.demo.crdts.invariants.examples;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.examples.jointbankaccount.JointBankAccount;
import de.tuda.stg.consys.invariants.lib.examples.messagegroups.Group;
import scala.Option;

import java.util.HashSet;
import java.util.Random;
import java.util.Set;

public class MessageGroupsBench extends CRDTBenchRunnable<Group> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-message-groups", MessageGroupsBench.class, args);
	}

	public MessageGroupsBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, Group.class);
	}

	private static String randStr(Random rand) {
		int len = rand.nextInt(10);
		String s = "";
		for (int i=0; i<len; i++) s += (char) (97+rand.nextInt(24));
		return s;
	}

	private static Set<String> randInbox(Random rand) {
		int len = rand.nextInt(10);
		Set<String> result = new HashSet<>();
		for (int i=0; i<len; i++) result.add(randStr(rand));
		return result;
	}

	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("postMessage", randStr(rand));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("addUser", rand.nextInt(Group.MAX_USER_ID), randInbox(rand));
					} catch (Exception e) {}
					return Option.apply(0);
				})
		});
	}


}
