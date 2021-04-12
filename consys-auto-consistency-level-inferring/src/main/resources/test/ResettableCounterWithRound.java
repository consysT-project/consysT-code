class ResettableCounterWithRound {

    /*@
    @ public invariant round >= 0;
    @ public invariant (\forall int i; i>=0 && i<numOfReplicas; incs[i] >= 0);
    @*/

    final int numOfReplicas = 12;
    final int replicaId = 11;

    int round = 0;
    int[] incs = new int[numOfReplicas];

    /*@
    @ ensures round == 0;
    @ ensures (\forall int init; init>=0 && init<numOfReplicas; incs[init] == 0);
    @*/
    public ResettableCounterWithRound() {}

    /*@
    @ ensures incs[replicaId] == \old(incs[replicaId]) + 1;
    @ ensures (\forall int b; b>=0 && b<numOfReplicas && b!=replicaId; incs[b] == \old(incs[b]));
    @ ensures round == \old(round);
    @*/
    void inc() {}


    /*@
    @ ensures round == \old(round) + 1;
    @ ensures (\forall int a; a>=0 && a<numOfReplicas; incs[a] == 0);
    @*/
    void reset() {}

    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int res; res>=0 && res<numOfReplicas; incs[res]);
    @*/
    int getValue() { return 0; }


    /*@
    @ requires (\old(round) == other.round) ==> \old(getValue()) == other.getValue();

    @ ensures (\old(round) < other.round) ==> (round == other.round) && (incs == other.incs);
    @ ensures (\old(round) > other.round) ==> (round == \old(round)) && (incs == \old(incs));
    @ ensures (\old(round) == other.round) ==> ((round == \old(round)) && (round == other.round));
    @
    @ ensures (\old(round) == other.round) && \old(getValue()) > other.getValue() ==> (incs == \old(incs));
    @ ensures (\old(round) == other.round) && \old(getValue()) < other.getValue() ==> (incs == other.incs);
    @ ensures (\old(round) == other.round) && \old(getValue()) == other.getValue() ==> ((incs == other.incs) && (incs == \old(incs)));
    @*/
    void merge(ResettableCounterWithRound other) {}
}