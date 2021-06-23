public class BankAccountWithReset {
    //@ public invariant balance >= 0;
    private int balance = 0;
    int timestamp = 0;



    /*@
    @ ensures balance == 0;
    @ ensures timestamp == 0;

    @*/
    public BankAccountWithReset() {}

    /*@
    @ requires amount >= 0;
    @ ensures balance == \old(balance) + amount;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void deposit(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        balance += amount;
        timestamp += 1;
    }

    /*@
    @ requires \old(balance) - amount >= 0;
    @ ensures balance == \old(balance) - amount;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void withdraw(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        balance -= amount;
        timestamp += 1;
    }

    /* In the CARD paper, reset is only "half-strong".
     * They can be executed with out coordination, if there is
     * no concurrent withdraws. Reset by itself does not violate
     * the invariant, hence resets only need to be executed with
     * strong consistency when there are withdraws.
     *
     * We cannot represent such effects in our system as
     * consistency is always symmetric (= withdraw and reset always have to
     * be executed strong). This is similar to Quelea or RedBlue.
     */

    /*@
    @ ensures balance == 0;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void reset() {
        balance = 0;
        timestamp += 1;
    }

    /*@
    @ requires \old(balance) >= 0;
    @ requires other.balance >= 0;
    @ requires \old(timestamp) == other.timestamp ==> \old(balance) == other.balance;

    @ ensures (\old(timestamp) > other.timestamp) ==> (balance == \old(balance)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) < other.timestamp) ==> (balance == other.balance) && (timestamp == other.timestamp);
    @ ensures (\old(timestamp) == other.timestamp) ==> (balance == \old(balance)) && (timestamp == \old(timestamp)) &&
                                                       (balance == other.balance) && (timestamp == other.timestamp);
    @*/
    public void merge(BankAccountWithReset other) {}
}
