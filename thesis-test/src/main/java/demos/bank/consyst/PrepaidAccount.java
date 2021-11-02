package demos.bank.consyst;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import java.util.LinkedList;

public @Strong class PrepaidAccount extends Account {
    public PrepaidAccount(Ref<@Weak LinkedList<String>> inbox) {
        messages = inbox;
    }

    @Transactional
    public void withdraw(@Strong int amount) {
        if (balance >= amount) {
            balance -= amount;
            messages.ref().add("New transaction: -" + amount);
        } else throw new IllegalArgumentException();
    }

    @Transactional
    public void deposit(@Strong int amount) {
        balance += amount;
        messages.ref().add("New transaction: +" + amount);
    }
}