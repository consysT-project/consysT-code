package demos.bank.java;

public class OverdraftAccount extends Account {
    @Override
    void withdraw(int amount) {
        balance -= amount;
        messages.add("New transaction: -" + amount);
    }

    @Override
    void deposit(int amount) {
        balance += amount;
        messages.add("New transaction: +" + amount);
    }
}
