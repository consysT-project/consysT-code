public class SideEffects {

    final int NOR = 15;

    /*@
    @ invariant value >= 0.0;
    @ invariant (\forall int inv; inv>=0 && inv<NOR; array[inv] >= 0.0);
    @*/

    double value;
    double[] array;

    /*@
    @ ensures value == 0.0;
    @ ensures array.length == NOR;
    @ ensures (\forall int init; init>=0 && init<NOR; array[init] == 0.0);
    @*/
    public SideEffects() {}

    /*@
    @ ensures value == \old(value) + 0.1;
    @ ensures array == \old(array);
    @ ensures \result == (\sum int y; y>=0&&y<NOR; array[y]);
    @*/
    public double yolo() { return 0.0;}


    /*@
    @ ensures value == other.value + \old(value);
    @ ensures (\forall int m; m>=0 && m<NOR;
                array[m] == \old(array[m]) + other.array[m]);
    @*/
    public void merge(SideEffects other) {}
}