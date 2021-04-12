public class CounterCRDT {
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
  public CounterCRDT() {}


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
  @ ensures incs[replicaId] == \old(incs[replicaId]) + 1;
  @ ensures (\forall int incI; incI>=0 && incI<numOfReplicas && incI != replicaId;
              incs[incI] == \old(incs[incI]));
  @ ensures decs == \old(decs);
  @*/
  void inc() {}

  /*@
  @ requires \old(getValue()) >= 1;
  @ ensures decs[replicaId] == \old(decs[replicaId]) + 1;
  @ ensures (\forall int decI; decI>=0 && decI<numOfReplicas && decI != replicaId;
              decs[decI] == \old(decs[decI]));
  @ ensures incs == \old(incs);
  @*/
  void dec() {}

  /*@
  @ ensures \old(sumIncs()) > other.sumIncs() ==> incs == \old(incs);
  @ ensures \old(sumIncs()) < other.sumIncs() ==> incs == other.incs;
  @ ensures \old(sumIncs()) == other.sumIncs()
              ==> incs == \old(incs) && incs == other.incs;
  @
  @ ensures \old(sumDecs()) > other.sumDecs() ==> decs == \old(decs);
  @ ensures \old(sumDecs()) < other.sumDecs() ==> decs == other.decs;
  @ ensures \old(sumDecs()) == other.sumDecs()
              ==> decs == \old(decs) && decs == other.decs;
  @*/
  void merge(CounterCRDT other) {}
}
