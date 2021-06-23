public class SimplestBankAccount {
    int value = 0;

    //@ public invariant value >= 0;

    /*@
    @ ensures value == 0;
    @*/
    public SimplestBankAccount() {}

    /*@
    @ ensures value == \old(value) + d;
    @*/
    public void deposit(int d) {}

    /*@
    @ ensures value == \old(value) - w;
    @*/
    public void withdraw(int w){}

    /*@
    @ ensures value == \old(value) || value == other.value;
    @*/
    public void merge(SimplestBankAccount other) {}
}