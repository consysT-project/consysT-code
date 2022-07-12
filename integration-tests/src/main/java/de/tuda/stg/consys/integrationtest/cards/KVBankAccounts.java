package de.tuda.stg.consys.integrationtest.cards;

import com.google.common.collect.Maps;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.Ref;

import java.util.Map;

public class KVBankAccounts {

    private final Map<Integer, Ref<@Mixed BankAccount>> accounts = Maps.newConcurrentMap();

    @WeakOp
    public void addAccount(int index, Ref<@Mixed BankAccount> account) {
        accounts.put(index, account);
    }

    @WeakOp
    @Transactional
    public void deposit(int index, int amount) {
        accounts.get(index).ref().deposit(amount);
    }

    @StrongOp
    @Transactional
    public void withdraw(int index, int amount) {
        accounts.get(index).ref().withdraw(amount);
    }
}
