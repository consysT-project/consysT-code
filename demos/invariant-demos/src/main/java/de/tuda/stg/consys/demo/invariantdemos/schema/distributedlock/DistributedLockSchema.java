package de.tuda.stg.consys.demo.invariantdemos.schema.distributedlock;

import de.tuda.stg.consys.bench.legacy.DistributedBenchmark;
import de.tuda.stg.consys.demo.invariantdemos.Schema;
import de.tuda.stg.consys.demo.invariantdemos.schema.creditaccount.ReplicatedCreditAccount;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.utils.InvariantUtils;

import java.util.Random;

public class DistributedLockSchema extends Schema<DistributedLock> {

	private final Random random = new Random();

	@Override
	public DistributedLock newInstance() {
		return new DistributedLock(InvariantUtils.replicaId());
	}

	@Override
	public Class<DistributedLock> instanceClass() {
		return DistributedLock.class;
	}

	@Override
	public void doOperation(JRef<DistributedLock> ref) {
		ref.invoke("transfer", random.nextInt(InvariantUtils.numOfReplicas() - 1) + 1);
	}


}
