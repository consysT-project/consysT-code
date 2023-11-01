public class Assignable {

    int a;
    double b;

    int[] c;
    float[] d;


    /*@
    @ ensures a == 0;
    @ ensures b == 0.0;
    @ ensures c.length == 5 && (\forall int i; i>=0 && i<5; c[i] == 0);
    @ ensures d.length == 10 && (\forall int j; j>=0 && j<10; d[j] == 0.0);
    @*/
    public Assignable() {super();}


    /*@
    @ assignable \nothing;
    @*/
    public void test1() {}


    /*@
    @ assignable a, b;
    @*/
    public void test2() {}

    /*@
    @ assignable c, d;
    @*/
    public void test3() {}

    /*@
    @ assignable c[3];
    @*/
    public void test4() {}


    /*@
    @ requires true;
    @ ensures true;
    @*/
    public void merge(Assignable other) {}



}