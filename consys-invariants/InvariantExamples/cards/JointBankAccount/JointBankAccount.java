import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

@ReplicatedModel public class JointBankAccount {
    //@ public invariant balance >= 0;
    private int balance = 0;
    int timestamp = 0;
    private boolean requested = false;
    private boolean approved = false;
    private int replicaId;

    /*@
    @ ensures balance == 0;
    @ ensures timestamp == 0;
    @ ensures requested == false;
    @ ensures approved == false;
    @ ensures replicaID == r;
    @*/
    public JointBankAccount(int r) {
        replicaId = r;
    }


    /*@
    @ requires amount >= 0;
    @ assignable balance, timestamp;
    @ ensures balance == \old(balance) + amount;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void deposit(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        balance += amount;
        timestamp += 1;
    }

    /*@
    @ requires balance - amount >= 0;
    @ requires approved == true;
    @ assignable balance, timestamp, approved, requested;
    @ ensures balance == \old(balance) - amount;
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures approved == false;
    @ ensures requested == false;
    @*/
    public void withdraw(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        if (!approved) throw new IllegalStateException("cannot withdraw from unapproved account");
        balance -= amount;
        reset();
        timestamp += 1;
    }

    /*@
    @ assignable timestamp, requested;
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures requested == true;
    @*/
    public void request() {
        requested = true;
        timestamp += 1;
    }

    /*@
    @ assignable approved, timestamp;
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures approved == \old(requested);
    @*/
    public void approve() {
        approved = requested;
        timestamp += 1;
    }

    /*@
    @ assignable approved, requested, timestamp;
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures approved == false;
    @ ensures requested == false;
    @*/
    public void reset() {
        requested = false;
        approved = false;
        timestamp += 1;
    }

    /*@
    @ ensures (\old(timestamp) > other.timestamp) ==> (balance == \old(balance)) && (timestamp == \old(timestamp) && approved == \old(approved)) && requested == \old(requested);
    @ ensures (\old(timestamp) < other.timestamp) ==> (balance == other.balance) && (timestamp == other.timestamp) && approved == other.approved && requested == other.requested;
    @ ensures (\old(timestamp) == other.timestamp) && (replicaId < other.replicaId) ==> (balance == \old(balance)) && (timestamp == \old(timestamp)) && approved == \old(approved) && requested == \old(requested);
    @ ensures (\old(timestamp) == other.timestamp) && (replicaId > other.replicaId) ==> (balance == other.balance) && (timestamp == other.timestamp) && approved == other.approved && requested == other.requested;
    @ ensures (\old(timestamp) == other.timestamp) && (replicaId == other.replicaId) ==> (balance == other.balance) && (timestamp == other.timestamp) && (balance == \old(balance)) && (timestamp == \old(timestamp)) && approved == other.approved && requested == other.requested && approved == \old(approved)) && requested == \old(requested);
    @*/
    public void merge(JointBankAccount other) {
        if (timestamp > other.timestamp || (timestamp == other.timestamp && replicaId < other.replicaId)) {
            // do not change this state
        } else {
            balance = other.balance;
            timestamp = other.timestamp;
            approved = other.approved;
            requested = other.requested;
        }
    }
}
