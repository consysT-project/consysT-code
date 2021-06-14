public class BankAccountCRDT {
    public static final int numOfReplicas = 10;


    /* Fields */
    public final int[] incs = new int[10];
    public final int[] decs = new int[10];
    public int replicaId;



    /* Invariants */
    /*@
    @ public invariant (\sum int inv0a; inv0a >= 0 && inv0a < numOfReplicas; incs[inv0a]) - (\sum int inv0b; inv0b >= 0 && inv0b < numOfReplicas; decs[inv0b]) >= 0;
    @ public invariant (\forall int inv1; inv1 >= 0 && inv1 < numOfReplicas; incs[inv1] >=0);
    @ public invariant (\forall int inv2; inv2 >= 0 && inv2 < numOfReplicas; decs[inv2] >=0);
    @ public invariant incs.length == numOfReplicas;
    @ public invariant decs.length == numOfReplicas;
    @*/


    /*@
    @ requires id >= 0 && id < numOfReplicas;
    @ ensures (\forall int init; init>=0 && init<numOfReplicas; incs[init] == 0 && decs[init] == 0);
    @ ensures replicaId == id;
    @*/
    public BankAccountCRDT(int id) {
        //super();
        this.replicaId = id;
    }


    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int incInd; incInd>=0 && incInd<numOfReplicas; incs[incInd]);
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
    @ ensures \result == (\sum int decInd; decInd>=0 && decInd<numOfReplicas; decs[decInd]);
    @*/
    public int sumDecs() {
        int result = 0;
        for (int dec : decs) {
            result += dec;
        }
        return result;
    }

    /*@ ensures \result == (\sum int valueIncInd; valueIncInd>=0 && valueIncInd < numOfReplicas; incs[valueIncInd]) - (\sum int valueDecInd; valueDecInd >= 0 && valueDecInd < numOfReplicas; decs[valueDecInd]);
    @ assignable \nothing;
    @*/
    public int getValue() {
        return sumIncs() - sumDecs();
    }



    /*@
    @ requires val >= 0;
    @ assignable incs[replicaId];
    @ ensures incs[replicaId] == \old(incs[replicaId]) + val;
    @ ensures (\forall int incI; incI>=0 && incI<numOfReplicas && incI != replicaId;
                incs[incI] == \old(incs[incI]));
    @ ensures (\forall int tempI; tempI>=0 && tempI<numOfReplicas;
                decs[tempI] == \old(decs[tempI]));
    @*/
    public void deposit(int val) {
        incs[replicaId] = incs[replicaId] + val;
    }

    /*@
    @ requires val >= 0;
    // requires getValue() >= val;
    @ requires  (\sum int withdrawIncInd; withdrawIncInd>=0 && withdrawIncInd < numOfReplicas; incs[withdrawIncInd]) - (\sum int withdrawDecInd; withdrawDecInd >= 0 && withdrawDecInd<numOfReplicas; decs[withdrawDecInd]) >= val;
    @ assignable decs[replicaId];
    @ ensures decs[replicaId] == \old(decs[replicaId]) + val;
    @ ensures (\forall int decI; decI>=0 && decI<numOfReplicas && decI != replicaId;
                decs[decI] == \old(decs[decI]));
    @ ensures (\forall int tempI2; tempI2>=0 && tempI2<numOfReplicas;
                incs[tempI2] == \old(incs[tempI2]));
    @*/
    public void withdraw(int val) {
        decs[replicaId] = decs[replicaId] + val;
    }

    /*@
    @ requires ((\sum int mergeI; mergeI >= 0 && mergeI < numOfReplicas;
            incs[mergeI] >= other.incs[mergeI] ? incs[mergeI] : other.incs[mergeI] )
             - (\sum int mergeI2; mergeI2>=0 && mergeI2<numOfReplicas;
                    decs[mergeI2] >= other.decs[mergeI2] ? decs[mergeI2] : other.decs[mergeI2] )) >= 0;

    @ ensures (\forall int mergeIncsI; mergeIncsI >= 0 && mergeIncsI < numOfReplicas;
                   (\old(incs[mergeIncsI]) >= other.incs[mergeIncsI] ==> incs[mergeIncsI] == \old(incs[mergeIncsI]))
                && (\old(incs[mergeIncsI]) <= other.incs[mergeIncsI] ==> incs[mergeIncsI] == other.incs[mergeIncsI])
                && (\old(decs[mergeIncsI]) >= other.decs[mergeIncsI] ==> decs[mergeIncsI] == \old(decs[mergeIncsI]))
                && (\old(decs[mergeIncsI]) <= other.decs[mergeIncsI] ==> decs[mergeIncsI] == other.decs[mergeIncsI])
               );
    @*/
    public void merge(BankAccountCRDT other) {
        for (int i = 0; i < numOfReplicas; i++) {
            incs[i] = incs[i] > other.incs[i] ? incs[i] : other.incs[i];
            decs[i] = decs[i] > other.decs[i] ? decs[i] : other.decs[i];
        }

    }



}