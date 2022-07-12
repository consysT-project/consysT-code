package demos.bank.consystop;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;

public @Mixed class OverdraftAccount extends Account {
    @Override @StrongOp
    public void withdraw(@Strong int amount) {
        balance -= amount;
        messages.add("New transaction: -" + amount);
    }

    @Override @StrongOp
    public void deposit(@Strong int amount) {
        balance += amount;
        messages.add("New transaction: +" + amount);
    }
}
