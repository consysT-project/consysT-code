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
		Option<Ref<@Mixed User>> result =
			store.<Ref<@Mixed User>>transaction(tx -> {
				Ref<@Mixed User> user = tx.replicate(user(userId), MIXED, (Class<@Mixed User>) User.class, name, replicaId());
				return Option.apply(user);
			});

		return result.<Ref<@Mixed User>>getOrElse(() -> null);
	}

	public Ref<@Mixed BankAccount> newAccount(int accId, Ref<@Mixed User> user) {
		Option<Ref<@Mixed BankAccount>> result = store.<Ref<@Mixed BankAccount>>transaction(tx -> {
			Ref<@Mixed BankAccount> account = tx.replicate(account(accId), MIXED, (Class<@Mixed BankAccount>)BankAccount.class, user, replicaId());
			return Option.apply(account);
		});

		return result.<Ref<@Mixed BankAccount>>getOrElse(() -> null);
	}


	public int getBalance(int accId) {
		var balance = store.transaction(tx -> {
			Ref<@Mixed BankAccount> account = tx.lookup(account(accId), MIXED, (Class<@Mixed BankAccount>)BankAccount.class);
			return Option.apply(account.ref().getBalance());
		});

		return balance.getOrElse(() -> -1);
	}


	public void transfer(int accId1, int accId2, int amount) {
		store.transaction(tx -> {
			Ref<@Mixed BankAccount> account1 = tx.lookup(account(accId1), MIXED, (Class<@Mixed BankAccount>)BankAccount.class);
			Ref<@Mixed BankAccount> account2 = tx.lookup(account(accId2), MIXED, (Class<@Mixed BankAccount>)BankAccount.class);
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

	private int replicaId() {
		return store.getId().name().hashCode();
	}

}
