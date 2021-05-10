package de.tuda.stg.consys.integrationtest.bank;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

public class Bank2 {

	private final CassandraStoreBinding store;

	public Bank2(CassandraStoreBinding store) {
		this.store = store;
	}

	public Ref<@Mixed User> newUser(int userId, String name) {
		var user = store.transaction(tx ->
			Option.apply(tx.replicate(user(userId), MIXED, User.class, name)));

		return user.getOrElse(() -> null);
	}

	public Ref<@Mixed BankAccount> newAccount(int accId, Ref<@Mixed User> user) {
		var account = store.transaction(tx ->
				Option.apply(tx.replicate(account(accId), MIXED, BankAccount.class, user)));

		return account.getOrElse(() -> null);
	}


	public int getBalance(int accId) {
		var balance = store.transaction(tx -> {
			var account = tx.lookup(account(accId), MIXED, BankAccount.class);
			return Option.apply(account.ref().getBalance());
		});

		return balance.getOrElse(() -> -1);
	}


	public void transfer(int accId1, int accId2, int amount) {
		store.transaction(tx -> {
			var account1 = tx.lookup(account(accId1), MIXED, BankAccount.class);
			var account2 = tx.lookup(account(accId2), MIXED, BankAccount.class);
			account1.ref().withdraw(amount);
			account2.ref().deposit(amount);
			return Option.empty();
		});
	}

	private String user(int id) {
		return "user$" + id;
	}

	private String account(int id) {
		return "account$" + id;
	}

}
