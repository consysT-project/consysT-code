package demos.bank.consyst;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import java.io.Serializable;
import java.util.LinkedList;

public abstract @Strong class Account implements Serializable {
    protected int balance;
    protected Ref<@Weak LinkedList<String>> messages;

    abstract public void withdraw(@Strong int amount);
    abstract public void deposit(@Strong int amount);

    public int getBalance() {
        return balance;
    }

    @Transactional
    public void addNewMessage(String msg) {
        messages.ref().add(msg);
    }

    @Transactional
    public String getInbox() {
        String s = "";
        for(String msg: messages.ref()) {
            s += msg + "\n";
        }
        return s;
    }
}