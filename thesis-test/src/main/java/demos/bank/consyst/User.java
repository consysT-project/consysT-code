package demos.bank.consyst;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

public @Strong class User implements Serializable {
    public boolean isActivated;
    private Ref<Bank> bank;
    private final String name;
    private List<Ref<? extends Account>> accounts = new LinkedList<>();

    public User(Ref<Bank> bank, @Strong String name) {
        this.bank = bank;
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public void addAccount(Ref<? extends Account> account, @Strong boolean asPrimary) {
        if (asPrimary) {
            accounts.add(0, account);
        } else {
            accounts.add(account);
        }
    }

    public Ref<? extends Account> getPrimaryAccount() {
        return accounts.get(0);
    }

    public List<Ref<? extends Account>> getAccounts() {
        return accounts;
    }

    @Transactional
    public void transferTo(Ref<User> receiver, @Strong int amount) {
        if (isActivated && (Boolean)receiver.ref().isActivated) {
            bank.ref().transfer(getPrimaryAccount(), receiver.ref().getPrimaryAccount(), amount);
        }
    }
}