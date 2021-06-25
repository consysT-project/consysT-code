public class CounterCRDT {
  public static final int numOfReplicas = 3;

    /*@
    @ public invariant (\sum int i; i >= 0 && i < numOfReplicas; incs[i]) - (\sum int i; i >= 0 && i < numOfReplicas; decs[i]) >= 0;
    @ public invariant (\forall int inv1; inv1>=0 && inv1<numOfReplicas;
                          incs[inv1] >=0);
    @ public invariant (\forall int inv2; inv2>=0 && inv2<numOfReplicas;
                          decs[inv2] >=0);
    @*/
    public int[] incs;
    public int[] decs;
    public int replicaId;

  /* Constructors */
  // Constructors define the initial state of an object.
  //@ requires id >= 0 && id < numOfReplicas;
  //@ ensures (\forall int i; i >= 0 && i < numOfReplicas; incs[i] == 0 && decs[i] == 0);
  //@ ensures replicaId == id;
  public CounterCRDT(int id) {
    if (!(id >= 0 && id < numOfReplicas))
      throw new IllegalArgumentException("id not in range.");

    this.incs = new int[numOfReplicas];
    this.decs = new int[numOfReplicas];
    this.replicaId = id;
  }


  /*@
  @ assignable \nothing;
  @ ensures \result ==
            (\sum int incInd; incInd>=0 && incInd<numOfReplicas; incs[incInd]);
  @*/
  int sumIncs() {
    int res = 0;
    for (int inc : incs) {
      res += inc;
    }
    return res;
  }

  /*@
  @ assignable \nothing;
  @ ensures \result ==
            (\sum int decInd; decInd>=0 && decInd<numOfReplicas; decs[decInd]);
  @*/
  int sumDecs(){
    int result = 0;
    for (int dec : decs) {
      result += dec;
    }
    return result;
  }

  /*@ assignable \nothing;
  @ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas; incs[i]) - (\sum int i; i >= 0 && i < numOfReplicas; decs[i]);
  @*/
  int getValue() { return sumIncs() - sumDecs(); }



  /*@
  @ assignable incs[replicaId];
  @ ensures incs[replicaId] == \old(incs[replicaId]) + 1;
  @*/
  void inc() {
    incs[replicaId] = incs[replicaId] + 1;
  }

  /*@
  @ requires (\sum int i; i >= 0 && i < numOfReplicas; incs[i]) - (\sum int i; i >= 0 && i < numOfReplicas; decs[i]) >= 1;
  @ assignable decs[replicaId];
  @ ensures decs[replicaId] == \old(decs[replicaId]) + 1;
  @*/
  void dec() {
    if (val > getValue())
      throw new IllegalArgumentException("not enough balance to withdraw");
    decs[replicaId] = decs[replicaId] + 1;
  }

  /*@
    @ requires ((\sum int i; i >= 0 && i < numOfReplicas; incs[i] >= other.incs[i] ? incs[i] : other.incs[i] )
             - (\sum int i; i >= 0 && i < numOfReplicas; decs[i] >= other.decs[i] ? decs[i] : other.decs[i] )) >= 0;
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas;
                   (\old(incs[i]) >= other.incs[i] ? incs[i] == \old(incs[i]) : incs[i] == other.incs[i])
                && (\old(decs[i]) >= other.decs[i] ? decs[i] == \old(decs[i]) : decs[i] == other.decs[i]));
    @ ensures replicaId == \old(replicaId);
  @*/
  void merge(CounterCRDT other) {
    for (int i = 0; i < numOfReplicas; i++) {
      incs[i] = Math.max(incs[i], other.incs[i]);
      decs[i] = Math.max(decs[i], other.decs[i]);
    }
  }
}
