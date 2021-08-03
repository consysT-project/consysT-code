public class SimpleCounter {

    public static final int numOfReplicas = 3;

    public SimpleNumber[] incs;
    public int replicaId;

    /* Constructors */
    // Constructors define the initial state of an object.
    //@ requires id >= 0 && id < numOfReplicas;
    //@ ensures (\forall int i; i >= 0 && i < numOfReplicas; incs[i].equals(0));
    //@ ensures replicaId == id;
    public SimpleCounter(int id) {
        if (!(id >= 0 && id < numOfReplicas))
        throw new IllegalArgumentException("id not in range.");
        this.incs = new SimpleNumber[numOfReplicas];
        for(int i = 0; i < numOfReplicas; ++i)
            incs.setValue(0);
    }

    /*@
    @ assignable \nothing;
    @ ensures \result ==
              (\sum int incInd; incInd>=0 && incInd<numOfReplicas; incs[incInd].getValue());
    @*/
    int sumIncs() {
        int res = 0;
        for (int i = 0; i < numOfReplicas; ++i) {
            res += incs[i].getValue();
        }
        return res;
    }

    /*@ assignable \nothing;
    @ ensures \result == sumIncs();
    @*/
    int getValue() { return sumIncs(); }



    /*@
    @ assignable incs[replicaId];
    @ ensures incs[replicaId].equals(\old(incs[replicaId].getValue())) + 1;
    @*/
    void inc() {
        incs[replicaId].modify(1);
    }

    // I use different approach here for testing another thing: \old(something).something()
    /*@
    @ requires n >= 0;
    @ assignable incs[replicaId];
    @ ensures incs[replicaId].equals(\old(incs[replicaId]).modify(n));
    @*/
    void inc(int n) {
        incs[replicaId].modify(n);
    }


    /*@
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas;
                     (\old(incs[i].getValue()) >= other.incs[i].getValue() ? incs[i].setValue(\old(incs[i].getValue())) : incs[i].setValue(other.incs[i].getValue()) ) );
    @ ensures replicaId == \old(replicaId);
    @*/
    void merge(GCounterCRDT other) {
        for (int i = 0; i < numOfReplicas; i++) {
            incs[i].setValue(Math.max(incs[i].getValue(), other.incs[i]).getValue());
        }
    }

}