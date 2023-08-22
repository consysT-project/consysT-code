package de.tuda.stg.consys.demo.messagegroups.schema.bank;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Weak;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

public @Mixed class BankAccount implements Serializable {

	private final List<@Immutable BankEvent> events;

	public BankAccount() {
		this.events = new LinkedList<>();
	}

	@StrongOp
	public void deposit(int amount) {
		events.add(new BankEvent.Deposit(amount));
	}

	@StrongOp
	public void withdraw(int amount) {
		events.add(new BankEvent.Withdraw(amount));
	}

	@SideEffectFree
	@WeakOp
	public int balance() {
		return events.stream().reduce(0, (integer, bankEvent) -> {
			if (bankEvent.isDeposit())
				return integer + bankEvent.getAmount();
			else
				return integer - bankEvent.getAmount();
		}, Integer::sum);
	}

	@SideEffectFree
	@WeakOp
	public @Immutable List<@Immutable BankEvent> getHistory() {
		return events;
	}
}
