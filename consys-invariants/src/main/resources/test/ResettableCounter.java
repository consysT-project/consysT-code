class ResettableCounter {

    //@ public invariant (\forall int inv; inv>=0 && inv<numOfReplicas; incs[inv] >= 0);
    final int numOfReplicas = 10;
    final int replicaId = 5;

    int[] incs = new int[10];

    /*@
    @ ensures (\forall int init; init>=0 && init<numOfReplicas; incs[init] == 0);
    @*/
    public ResettableCounter() {}

    /*@
    @ ensures incs[replicaId] == (\old(incs[replicaId]) + 1);
    @ ensures (\forall int incInd; incInd>=0 && incInd<numOfReplicas && incInd!=replicaId; incs[incInd] == \old(incs[incInd]));
    @*/
    void inc() {}

    /*@
    @ ensures (\forall int a; 0<=a && a<numOfReplicas; incs[a] == 0);
    @*/
    void reset() {}


    //@ ensures \result == (\sum int b; b>=0 && b<numOfReplicas; incs[b]);
    //@ assignable \nothing;
    int getValue() { return 0; }


    /*@
    @ requires (\forall int m1; m1>=0 && m1<numOfReplicas; \old(incs[m1]) >= 0);
    @ requires (\forall int m2; m2>=0 && m2<numOfReplicas; other.incs[m2] >= 0);

    @ ensures \old(getValue()) > other.getValue() ==> (incs == \old(incs));
    @ ensures \old(getValue()) < other.getValue() ==> (incs == other.incs);
    @ ensures \old(getValue()) == other.getValue() ==> (incs == other.incs) && (incs == \old(incs));
    @*/
    void merge(ResettableCounter other) {
        //incs = max(incs, other.incs);
    }
}