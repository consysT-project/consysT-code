package demos.bank.java;

import java.util.*;

public abstract class Account {
    protected int balance;
    protected List<String> messages = new LinkedList<>();

    abstract void withdraw(int amount);
    abstract void deposit(int amount);

    int getBalance() {
        return balance;
    }

    public void addNewMessage(String msg) {
        messages.add(msg);
    }

    public String getInbox() {
        String s = "";
        for(String msg: messages) {
            s += msg + "\n";
        }
        return s;
    }
}