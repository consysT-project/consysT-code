package demos.bank.consystop;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;
import java.io.*;
import java.util.*;

public @Mixed class Bank implements Serializable {
    private @Immutable String id;
    private List<Ref<User>> users = new ArrayList<>();
    private List<Ref<? extends Account>> accounts = new ArrayList<>();

    public Bank(@Strong String id) {
        this.id = id;
    }

    @Transactional @StrongOp
    public Ref<User> registerUser(String name, @Mutable CassandraTransactionContextBinding ctx) {
        Ref<Bank> thisBank = ctx.lookup(id, MIXED, Bank.class);
        Ref<User> user = ctx.replicate(name, STRONG, User.class, thisBank, name);
        users.add(user);
        return user;
    }

    @Transactional @StrongOp
    public Ref<? extends Account> registerPrepaidAccount(Ref<@Mutable User> user, @Mutable CassandraTransactionContextBinding ctx) {
        @Immutable String name = (String)user.ref().getName() + "-" + ((@Mutable List<Ref<? extends Account>>) user.ref().getAccounts()).size();
        Ref<? extends @Mutable Account> account = ctx.replicate(name, MIXED, PrepaidAccount.class);
        user.ref().addAccount(account, false);
        user.ref().isActivated = true;
        accounts.add(account);
        return account;
    }

    @Transactional @StrongOp
    public Ref<? extends Account> registerOverdraftAccount(Ref<@Mutable User> user, @Mutable CassandraTransactionContextBinding ctx) {
        @Immutable String name = (String)user.ref().getName() + "-" + ((@Mutable List<Ref<? extends Account>>) user.ref().getAccounts()).size();
        Ref<? extends @Mutable Account> account = ctx.replicate(name, MIXED, OverdraftAccount.class);
        user.ref().addAccount(account, false);
        user.ref().isActivated = true;
        accounts.add(account);
        return account;
    }

    public List<Ref<User>> getUsers() {
        return users;
    }

    @Transactional
    public void transfer(Ref<? extends @Mutable Account> sender, Ref<? extends @Mutable Account> receiver, @Strong int amount) {
        try {
            sender.ref().withdraw(amount);
            receiver.ref().deposit(amount);
        } catch (IllegalArgumentException e) {
            ((@Mutable PrintStream)System.out).println("Transaction invalid");
        }
    }

    @Transactional
    public void publishSystemMessage(String message) {
        for (Ref<? extends @Mutable Account> account : accounts) {
            account.ref().addNewMessage(message);
        }
    }
}
