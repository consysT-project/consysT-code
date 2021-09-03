package de.tuda.stg.consys.demo.invariantdemos.schema.bankaccount;

import de.tuda.stg.consys.demo.invariantdemos.Schema;
import de.tuda.stg.consys.japi.legacy.JRef;

import java.util.Random;

public class BankAccountSchema extends Schema<BankAccount> {
	private final Random random = new Random();

	@Override
	public BankAccount newInstance() {
		return new BankAccount();
	}

	@Override
	public Class<BankAccount> instanceClass() {
		return BankAccount.class;
	}

	@Override
	public void doOperation(JRef<BankAccount> ref) {
		int rand = random.nextInt(100);
		if (rand < 25) {
			ref.ref().deposit(100);
		} else if (rand < 50) {
			ref.ref().withdraw(1);
		} else if (rand < 75) {
			ref.ref().getValue();
		} else if (rand < 100) {
			ref.ref().reset();
		}
	}
}
