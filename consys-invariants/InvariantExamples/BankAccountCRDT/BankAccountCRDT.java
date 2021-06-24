public class BankAccountCRDT {
    /* Constants */
    // Constants have to be declared with static final.
    public static final int numOfReplicas = 3;


    /* Fields */
    // Virtual fields that can be accessed in constraints with `this`.
    public final int[] incs = new int[numOfReplicas];
    public final int[] decs = new int[numOfReplicas];
    public int replicaId;



    /* Invariants */
    /*@
    @ public invariant (\sum int i; i >= 0 && i < numOfReplicas; incs[i]) - (\sum int i; i >= 0 && i < numOfReplicas; decs[i]) >= 0;
    @ public invariant (replicaId >= 0) && (replicaId < numOfReplicas);
    @*/


    /*@
    @ requires id >= 0 && id < numOfReplicas;
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas; incs[i] == 0 && decs[i] == 0);
    @ ensures replicaId == id;
    @*/
    public BankAccountCRDT(int id) {
        //super();
        this.replicaId = id;
    }

    //@ assignable replicaId;
    //@ ensures replicaId == id;
    public void setReplicaId(int id) {
        this.replicaId = id;
    }

    //@ assignable incs;
    //@ ensures (\forall int i; i >= 0 && i < numOfReplicas; incs[i] == 0);
    public void resetIncs() {
        for (int i = 0; i < incs.length; i++) {
            incs[i] = 0;
        }
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas; incs[i]);
    @*/
    public int sumIncs() {
        int res = 0;
        for (int inc : incs) {
            res += inc;
        }
        return res;
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas; decs[i]);
    @*/
    public int sumDecs() {
        int result = 0;
        for (int dec : decs) {
            result += dec;
        }
        return result;
    }

    /*@ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas; incs[i]) - (\sum int i; i >= 0 && i < numOfReplicas; decs[i]);
    @ assignable \nothing;
    @*/
    public int getValue() {
        return sumIncs() - sumDecs();
    }



    /*@
    @ requires val >= 0;
    @ assignable incs[replicaId];
    @ ensures incs[replicaId] == \old(incs[replicaId]) + val;
    @*/
    public void deposit(int val) {
        incs[replicaId] = incs[replicaId] + val;
    }

    /*@
    @ requires val >= 0;
    @ requires  (\sum int i; i >= 0 && i < numOfReplicas; incs[i]) - (\sum int i; i >= 0 && i < numOfReplicas; decs[i]) >= val;
    @ assignable decs[replicaId];
    @ ensures decs[replicaId] == \old(decs[replicaId]) + val;
    @*/
    public void withdraw(int val) {
        decs[replicaId] = decs[replicaId] + val;
    }

    /*@
    @ requires ((\sum int i; i >= 0 && i < numOfReplicas; incs[i] >= other.incs[i] ? incs[i] : other.incs[i] )
             - (\sum int i; i >= 0 && i < numOfReplicas; decs[i] >= other.decs[i] ? decs[i] : other.decs[i] )) >= 0;
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas;
                   (\old(incs[i]) >= other.incs[i] ? incs[i] == \old(incs[i]) : incs[i] == other.incs[i])
                && (\old(decs[i]) >= other.decs[i] ? decs[i] == \old(decs[i]) : decs[i] == other.decs[i]));
    @ ensures replicaId == \old(replicaId);
    @*/
    public void merge(BankAccountCRDT other) {
        for (int i = 0; i < numOfReplicas; i++) {
            incs[i] = incs[i] > other.incs[i] ? incs[i] : other.incs[i];
            decs[i] = decs[i] > other.decs[i] ? decs[i] : other.decs[i];
        }
    }
}