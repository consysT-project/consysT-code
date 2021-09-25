package demos.bank.java;

public class PrepaidAccount extends Account {
    @Override
    void withdraw(int amount) {
        if (balance >= amount) {
            balance -= amount;
            messages.add("New transaction: -" + amount);
        } else throw new IllegalArgumentException();
    }

    @Override
    void deposit(int amount) {
        balance += amount;
        messages.add("New transaction: +" + amount);
    }
}
