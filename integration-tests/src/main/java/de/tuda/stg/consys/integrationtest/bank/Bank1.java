package de.tuda.stg.consys.integrationtest.bank;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Bank1 {

	private final Set<Ref<@Mixed BankAccount>> accounts = new HashSet<>();
	private final Set<Ref<@Mixed User>> users = new HashSet<>();

	public Bank1() {}

	public void newUser(Ref<@Mixed User> user) {
		users.add(user);
	}

	public void newAccount(Ref<@Mixed BankAccount> account) {
		accounts.add(account);
	}

	@Transactional
	public void transfer(Ref<@Mixed BankAccount> account1, Ref<@Mixed BankAccount> account2, int amount) {
		account1.ref().withdraw(amount);
		account2.ref().deposit(amount);
	}

}
