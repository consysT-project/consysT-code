package de.tuda.stg.consys.demo.invariantdemos.schema.creditaccount;

import de.tuda.stg.consys.demo.invariantdemos.Schema;
import de.tuda.stg.consys.japi.legacy.JRef;

import java.util.Random;

public class ReplicatedCreditAccountSchema extends Schema<ReplicatedCreditAccount> {

	private final Random random = new Random();

	@Override
	public ReplicatedCreditAccount newInstance() {
		ReplicatedCreditAccount result = new ReplicatedCreditAccount();
		result.deposit(10000000);
		return result;
	}

	@Override
	public Class<ReplicatedCreditAccount> instanceClass() {
		return ReplicatedCreditAccount.class;
	}

	@Override
	public void doOperation(JRef<ReplicatedCreditAccount> ref) {
		int rand = random.nextInt(100);
		if (rand < 33) {
			ref.ref().deposit(100);
		} else if (rand < 66) {
			ref.ref().withdraw(1);
		} else if (rand < 100) {
			ref.ref().getValue();
		}
	}
}
