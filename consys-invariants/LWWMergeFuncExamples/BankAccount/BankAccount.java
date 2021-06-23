public class BankAccount {

    int value = 0;
    int timestamp = 0;

    final int replicaId = 3;

    //@ public invariant value >= 0;

    /*@
    @ ensures value == 0;
    @ ensures timestamp == 0;
    @*/
    public BankAccount() {}

    /*@
    @ requires d >= 0;
    @ ensures value == \old(value) + d;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void deposit(int d) {}

    /*@
    @ requires \old(value) - w >= 0;
    @ ensures value == \old(value) - w;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    public void withdraw(int w){}

    /*@
    @ requires \old(value) >= 0;
    @ requires other.value >= 0;

    @ ensures (\old(timestamp) > other.timestamp) ==> (value == \old(value)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) < other.timestamp) ==> (value == other.value) && (timestamp == other.timestamp);
    @ ensures (\old(timestamp) == other.timestamp && replicaId < other.replicaId ) ==> (value == \old(value)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) == other.timestamp && replicaId > other.replicaId ) ==> (value == other.value) && (timestamp == other.timestamp);
    @ ensures (\old(timestamp) == other.timestamp && replicaId == other.replicaId ) ==> (value == \old(value)) && (timestamp == \old(timestamp)) && (value == other.value) && (timestamp == other.timestamp);

    @*/
    public void merge(BankAccount other) {}
}
