public class BankAccountCRDT {
    public static final int numOfReplicas = 10;
    public static final int replicaId = 5;

    /*@
    @ public invariant getValue() >= 0;
    @ public invariant (\forall int inv1; inv1>=0 && inv1<numOfReplicas;
                          incs[inv1] >=0);
    @ public invariant (\forall int inv2; inv2>=0 && inv2<numOfReplicas;
                          decs[inv2] >=0);
    @*/
    int[] incs = new int[numOfReplicas];
    int[] decs = new int[numOfReplicas];

    /*@
    @ ensures (\forall int init; init>=0 && init<numOfReplicas;
                (incs[init] == 0) && (decs[init] == 0));
    @*/
    public BankAccountCRDT() {}


    /*@
    @ assignable \nothing;
    @ ensures \result ==
              (\sum int incInd; incInd>=0 && incInd<numOfReplicas; incs[incInd]);
    @*/
    int sumIncs() { return 0; }

    /*@
    @ assignable \nothing;
    @ ensures \result ==
              (\sum int decInd; decInd>=0 && decInd<numOfReplicas; decs[decInd]);
    @*/
    int sumDecs(){ return 0; }

    /*@ ensures \result == sumIncs() - sumDecs();
    @ assignable \nothing;
    @*/
    int getValue() { return 0; }



    /*@
    @ requires val >= 0;
    @ ensures incs[replicaId] == \old(incs[replicaId]) + val;
    @ ensures (\forall int incI; incI>=0 && incI<numOfReplicas && incI != replicaId;
                incs[incI] == \old(incs[incI]));
    @ ensures (\forall int tempI; tempI>=0 && tempI<numOfReplicas;
                decs[tempI] == \old(decs[tempI]));
    @*/
    void deposit(int val) {}

    /*@
    @ requires val >= 0;
    @ requires \old(getValue()) >= val;
    @ ensures decs[replicaId] == \old(decs[replicaId]) + val;
    @ ensures (\forall int decI; decI>=0 && decI<numOfReplicas && decI != replicaId;
                decs[decI] == \old(decs[decI]));
    @ ensures (\forall int tempI2; tempI2>=0 && tempI2<numOfReplicas;
                incs[tempI2] == \old(incs[tempI2]));
    @*/
    void withdraw(int val) {}

    /*@
    @ requires (\sum int mergeI; mergeI>=0 && mergeI<numOfReplicas;
                    \old(incs[mergeI])>other.incs[mergeI] ? \old(incs[mergeI]) : other.incs[mergeI] )
               - (\sum int mergeI2; mergeI2>=0 && mergeI2<numOfReplicas;
                    \old(decs[mergeI2])>other.decs[mergeI2] ? \old(decs[mergeI2]) : other.decs[mergeI2] ) >= 0;
    @ ensures (\forall int mergeIncsI; mergeIncsI>=0 && mergeIncsI<numOfReplicas;
                    (\old(incs[mergeIncsI]) >= other.incs[mergeIncsI] ==> incs[mergeIncsI] == \old(incs[mergeIncsI]))
                &&  (\old(incs[mergeIncsI]) <= other.incs[mergeIncsI] ==> incs[mergeIncsI] == other.incs[mergeIncsI]) );
    @ ensures (\forall int mergeDecsI; mergeDecsI>=0 && mergeDecsI<numOfReplicas;
                    (\old(decs[mergeDecsI]) >= other.decs[mergeDecsI] ==> decs[mergeDecsI] == \old(decs[mergeDecsI]))
                &&  (\old(decs[mergeDecsI]) <= other.decs[mergeDecsI] ==> decs[mergeDecsI] == other.decs[mergeDecsI]) );
    @*/
    void merge(BankAccountCRDT other) {}
}

/*
    @ requires (\sum int mergeI; mergeI>=0 && mergeI<numOfReplicas;
                    ((\old(incs[mergeI]) > other.incs[mergeI]) ? \old(incs[mergeI]) : other.incs[mergeI]) )
               - (\sum int mergeI2; mergeI2>=0 && mergeI2<numOfReplicas;
                    ((\old(decs[mergeI2]) > other.decs[mergeI2]) ? \old(decs[mergeI2]) : other.decs[mergeI2]) ) >= 0;
 */