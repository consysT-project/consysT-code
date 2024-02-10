public class SimpleBankAccount {

    int value = 0;

    //@ public invariant value >= 0;

    /*@
    @ ensures value == 0;
    @*/
    public SimpleBankAccount() {}

    /*@
    @ requires d >= 0;
    @ ensures value == \old(value) + d;
    @*/
    public void deposit(int d) {}

    /*@
    @ requires \old(value) - w >= 0;
    @ ensures value == \old(value) - w;
    @*/
    public void withdraw(int w){}

    /*@
    @ requires \old(value) >= 0;
    @ requires other.value >= 0;
    @ ensures value == \old(value) || value == other.value;
    @*/
    public void merge(SimpleBankAccount other) {}
}
