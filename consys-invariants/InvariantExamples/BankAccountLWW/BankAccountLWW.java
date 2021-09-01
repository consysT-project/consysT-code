import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

@ReplicatedModel public class BankAccountLWW {

    int value = 0;
    int timestamp = 0;
    int id;

    //@ public invariant value >= 0;

    /*@
    @ ensures value == 0;
    @ ensures timestamp == 0;
    @ ensures this.id == id;
    @*/
    public BankAccountLWW(int id) {
        this.id = id;
    }

    /*@
    @ requires d >= 0;
    @ assignable value, timestamp;
    @ ensures value == \old(value) + d;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void deposit(int d) {
        value = value + d;
        timestamp = timestamp + 1;
    }

    /*@
    @ requires value - w >= 0;
    @ assignable value, timestamp;
    @ ensures value == \old(value) - w;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void withdraw(int w) {
        if (value - w < 0)
            throw new IllegalArgumentException("not enough money on account");

        value = value - w;
        timestamp = timestamp + 1;
    }

    /*@
    @ ensures (\old(timestamp) > other.timestamp) ==> (value == \old(value)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) < other.timestamp) ==> (value == other.value) && (timestamp == other.timestamp);
    @ ensures (\old(timestamp) == other.timestamp) && (id < other.id) ==> (value == \old(value)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) == other.timestamp) && (id > other.id) ==> (value == other.value) && (timestamp == other.timestamp);
    ensures (\old(timestamp) == other.timestamp) && (id == other.id) ==> (value == other.value) && (timestamp == other.timestamp) && (value == \old(value)) && (timestamp == \old(timestamp));
    @*/
    public void merge(BankAccountLWW other) {
        if (timestamp > other.timestamp || (timestamp == other.timestamp && id < other.id)) {
            // do not change this state
        } else {
            value = other.value;
            timestamp = other.timestamp;
        }
    }
}
