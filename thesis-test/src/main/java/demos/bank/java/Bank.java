package demos.bank.java;

import java.util.*;

public class Bank {
    private List<User> users = new LinkedList<>();
    private List<Account> accounts = new LinkedList<>();

    public User registerUser(String name) {
        User user = new User(this, name);
        users.add(user);
        return user;
    }

    public Account registerPrepaidAccount(User user) {
        Account account = new PrepaidAccount();
        user.addAccount(account, false);
        user.isActivated = true;
        accounts.add(account);
        return account;
    }

    public Account registerOverdraftAccount(User user) {
        Account account = new OverdraftAccount();
        user.addAccount(account, false);
        user.isActivated = true;
        accounts.add(account);
        return account;
    }

    public List<User> getUsers() {
        return users;
    }

    public void transfer(Account sender, Account receiver, int amount) {
        try {
            sender.withdraw(amount);
            receiver.deposit(amount);
        } catch (IllegalArgumentException e) {
            System.out.println("Transaction invalid");
        }
    }

    public void publishSystemMessage(String message) {
        for (Account account : accounts) {
            account.addNewMessage(message);
        }
    }
}
