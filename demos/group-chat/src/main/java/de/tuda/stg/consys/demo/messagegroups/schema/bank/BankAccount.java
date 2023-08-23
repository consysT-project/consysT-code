package de.tuda.stg.consys.demo.messagegroups.schema.bank;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

public @Mixed class BankAccount implements Serializable {

	private Ref<@Strong User> owner;
	private List<BalanceChange> events;

	public BankAccount() {
		this.events = new LinkedList<>();
	}

	@StrongOp
	public void deposit(int amount) {
		events.add(new BalanceChange(amount));
	}

	@StrongOp
	public void withdraw(int amount) {
		events.add(new BalanceChange(-amount));
	}


	@WeakOp
	@SideEffectFree
	public int balance() {
		return events.stream().mapToInt(BalanceChange::getAmount).sum();
	}

	@SideEffectFree
	@WeakOp
	public List<BalanceChange> getHistory() {
		return events;
	}
}
