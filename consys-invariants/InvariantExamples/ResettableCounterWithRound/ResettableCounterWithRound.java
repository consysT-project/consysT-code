class ResettableCounterWithRound {

    /*@
    @ public invariant round >= 0;
    @ public invariant (\forall int inv; inv>=0 && inv<numOfReplicas; incs[inv] >= 0);
    @*/
    public static final int numOfReplicas = 10;
    final int replicaId = 3;

    int[] incs;
    int round;

    /*@
    @ ensures round == 0;
    @ ensures (\forall int init; init>=0 && init<numOfReplicas; incs[init] == 0);
    @*/
    public ResettableCounterWithRound() {
        incs = new int[numOfReplicas];
        round = 0;
    }

    /*@
    @ assignable incs[replicaId];
    @ ensures incs[replicaId] == \old(incs[replicaId]) + 1;
    @ ensures (\forall int b; b>=0 && b<numOfReplicas && b!=replicaId; incs[b] == \old(incs[b]));
    @ ensures round == \old(round);
    @*/
    void inc() { incs[replicaId] = incs[replicaId] + 1;}


    /*@
    @ assingable round, incs;
    @ ensures round == \old(round) + 1;
    @ ensures (\forall int a; a>=0 && a<numOfReplicas; incs[a] == 0);
    @*/
    void reset() {
        round += 1;
        for(int i = 0; i < numOfReplicas; ++i)
            incs[i] = 0;
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int res; res>=0 && res<numOfReplicas; incs[res]);
    @*/
    int getValue() {
        int val = 0;
        for(int i = 0; i < numOfReplicas; ++i)
            val += incs[i];
        return val;
    }


    /*@
    @ requires (\old(round) == other.round) ==> (\sum int res; res>=0 && res<numOfReplicas; \old(incs[res])) == (\sum int res; res>=0 && res<numOfReplicas; other.incs[res]);
    @ ensures (\old(round) < other.round) ==> (round == other.round) && (\forall int i; i >= 0 && i<numOfReplicas; incs[i] == other.incs[i]);
    @ ensures (\old(round) > other.round) ==> (round == \old(round)) && (\forall int i; i >= 0 && i<numOfReplicas; incs[i] == \old(incs[i]));
    @ ensures (\old(round) == other.round) ==> ((round == \old(round)) && (round == other.round)) && (\forall int i; i >= 0 && i < numOfReplicas;
                                                                                   (\old(incs[i]) >= other.incs[i] ? incs[i] == \old(incs[i]) : incs[i] == other.incs[i]));
    @*/
    void merge(ResettableCounterWithRound other) {
        if(round < other.round) {
            round = other.round;
            for (int i = 0; i < numOfReplicas; i++)
                incs[i] = other.incs[i];
        }
        else if (round == other.round) {
            for (int i = 0; i < numOfReplicas; i++)
                incs[i] = Math.max(incs[i], other.incs[i]);
        }
    }
}