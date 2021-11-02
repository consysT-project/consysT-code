package demos.bank.consyst;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;
import java.io.Serializable;
import java.util.*;

public @Strong class Bank implements Serializable {
    private String id;
    private List<Ref<User>> users = new ArrayList<>();
    private List<Ref<? extends Account>> accounts = new ArrayList<>();

    public Bank(@Strong String id) {
        this.id = id;
    }

    @Transactional
    public Ref<User> registerUser(String name, CassandraTransactionContextBinding ctx) {
        Ref<Bank> thisBank = ctx.lookup(id, STRONG, Bank.class);
        Ref<User> user = ctx.replicate(name, WEAK, User.class, thisBank, name);
        users.add(user);
        return user;
    }

    @Transactional
    public Ref<? extends Account> registerPrepaidAccount(Ref<User> user, CassandraTransactionContextBinding ctx) {
        String name = (String)user.ref().getName() + "-" + ((List<? extends Account>) user.ref().getAccounts()).size();
        Ref<LinkedList<String>> inbox = ctx.replicate(name + "-inbox", WEAK, (Class<LinkedList<String>>)(Object)LinkedList.class);
        Ref<? extends Account> account = ctx.replicate(name, STRONG, PrepaidAccount.class, inbox);
        user.ref().addAccount(account, false);
        user.ref().isActivated = true;
        accounts.add(account);
        return account;
    }

    @Transactional
    public Ref<? extends Account> registerOverdraftAccount(Ref<User> user, CassandraTransactionContextBinding ctx) {
        String name = (String)user.ref().getName() + "-" + ((List<? extends Account>) user.ref().getAccounts()).size();
        Ref<LinkedList<String>> inbox = ctx.replicate(name + "-inbox", WEAK, (Class<LinkedList<String>>)(Object)LinkedList.class);
        Ref<? extends Account> account = ctx.replicate(name, STRONG, OverdraftAccount.class, inbox);
        user.ref().addAccount(account, false);
        user.ref().isActivated = true;
        accounts.add(account);
        return account;
    }

    public List<Ref<User>> getUsers() {
        return users;
    }

    @Transactional
    public void transfer(Ref<? extends Account> sender, Ref<? extends Account> receiver, @Strong int amount) {
        try {
            sender.ref().withdraw(amount);
            receiver.ref().deposit(amount);
        } catch (IllegalArgumentException e) {
            System.out.println("Transaction invalid");
        }
    }

    @Transactional
    public void publishSystemMessage(String message) {
        for (Ref<? extends Account> account : accounts) {
            account.ref().addNewMessage(message);
        }
    }
}