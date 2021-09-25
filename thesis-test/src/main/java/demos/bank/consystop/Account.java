package demos.bank.consystop;

import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import java.io.Serializable;
import java.util.*;

public abstract @Mixed class Account implements Serializable {
    protected int balance;
    protected List<String> messages = new LinkedList<>();

    @StrongOp
    abstract public void withdraw(@Strong int amount);
    @StrongOp
    abstract public void deposit(@Strong int amount);

    public int getBalance() {
        return balance;
    }

    @WeakOp
    public void addNewMessage(String msg) {
        messages.add(msg);
    }

    public @Inconsistent String getInbox() {
        @Immutable String s = "";
        for(@Immutable String msg: messages) {
            s += msg + "\n";
        }
        return s;
    }
}
