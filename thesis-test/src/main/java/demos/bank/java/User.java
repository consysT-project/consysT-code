package demos.bank.java;

import java.util.*;

public class User {
    public boolean isActivated;
    private final Bank bank;
    private final String name;
    private List<Account> accounts = new LinkedList<>();

    public User(Bank bank, String name) {
        this.bank = bank;
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public void addAccount(Account account, boolean asPrimary) {
        if (asPrimary) {
            accounts.add(0, account);
        } else {
            accounts.add(account);
        }
    }

    public Account getPrimaryAccount() {
        return accounts.get(0);
    }

    public List<Account> getAccounts() {
        return accounts;
    }

    public void transferTo(User receiver, int amount) {
        if (isActivated && receiver.isActivated) {
            bank.transfer(getPrimaryAccount(), receiver.getPrimaryAccount(), amount);
        }
    }
}
