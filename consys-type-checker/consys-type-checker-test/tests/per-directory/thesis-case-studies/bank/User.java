package demos.bank.consystop;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;
import java.io.Serializable;
import java.util.*;

public @Strong class User implements Serializable {
    public boolean isActivated;
    private Ref<@Mutable Bank> bank;
    private final @Immutable String name;
    private List<Ref<? extends @Mutable Account>> accounts = new LinkedList<>();

    public User(Ref<@Mutable Bank> bank, @Strong String name) {
        this.bank = bank;
        this.name = name;
    }

    @SideEffectFree
    public String getName() {
        return name;
    }

    public void addAccount(Ref<? extends @Mutable Account> account, @Strong boolean asPrimary) {
        if (asPrimary) {
            accounts.add(0, account);
        } else {
            accounts.add(account);
        }
    }

    @SideEffectFree
    public Ref<? extends @Mutable Account> getPrimaryAccount() {
        return accounts.get(0);
    }

    public List<Ref<? extends @Mutable Account>> getAccounts() {
        return accounts;
    }

    @Transactional
    public void transferTo(Ref<@Mutable User> receiver, @Strong int amount) {
        if (isActivated && (Boolean)receiver.ref().isActivated) {
            bank.ref().transfer(getPrimaryAccount(), receiver.ref().getPrimaryAccount(), amount);
        }
    }
}
