package de.tuda.stg.consys.demo.groupchat.schema.bank;


import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public @Mixed class Bank implements Serializable {

	private Map<Integer, Ref<@Mutable BankAccount>> accounts;

	public Bank() {
		accounts = new HashMap<>();
	}

	@Transactional
	@StrongOp
	public void transfer(int fromId, int toId, int amount) {
		Ref<@Mutable BankAccount> fromAccount = accounts.get(fromId);
		Ref<@Mutable BankAccount> toAccount = accounts.get(toId);

		fromAccount.ref().withdraw(amount);
		toAccount.ref().deposit(amount);
	}

	@Transactional
	@WeakOp
	public void detectFraud() {
		for (var account : accounts.values()) {
			checkHistory(account.ref().getHistory());
		}
	}

	private boolean checkHistory(List<BalanceChange> history) {
		return false;
	}
}
