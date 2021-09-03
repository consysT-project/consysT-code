import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

@ReplicatedModel public class PNCounterCRDT {
  public static final int numOfReplicas = 3;


    public int[] incs;
    public int[] decs;
    public int replicaId;

  /* Constructors */
  // Constructors define the initial state of an object.
  //@ requires id >= 0 && id < numOfReplicas;
  //@ ensures (\forall int i; i >= 0 && i < numOfReplicas; incs[i] == 0 && decs[i] == 0);
  //@ ensures replicaId == id;
  public PNCounterCRDT(int id) {
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
  @ ensures \result == sumIncs() - sumDecs();
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
  @ requires n >= 0;
  @ assignable incs[replicaId];
  @ ensures incs[replicaId] == \old(incs[replicaId]) + n;
  @*/
  void inc(int n) {
    incs[replicaId] = incs[replicaId] + n;
  }

  /*@
  @ assignable decs[replicaId];
  @ ensures decs[replicaId] == \old(decs[replicaId]) + 1;
  @*/
  void dec() {
    if (1 > getValue())
      throw new IllegalArgumentException("not enough balance to withdraw");
    decs[replicaId] = decs[replicaId] + 1;
  }

  /*@
  @ requires n >= 0;
  @ assignable decs[replicaId];
  @ ensures decs[replicaId] == \old(decs[replicaId]) + n;
  @*/
  void dec(int n) {
    if (n > getValue())
      throw new IllegalArgumentException("not enough balance to withdraw");
    decs[replicaId] = decs[replicaId] + n;
  }

  /*@
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas;
                   (\old(incs[i]) >= other.incs[i] ? incs[i] == \old(incs[i]) : incs[i] == other.incs[i])
                && (\old(decs[i]) >= other.decs[i] ? decs[i] == \old(decs[i]) : decs[i] == other.decs[i]));
    @ ensures replicaId == \old(replicaId);
  @*/
  void merge(PNCounterCRDT other) {
    for (int i = 0; i < numOfReplicas; i++) {
      incs[i] = Math.max(incs[i], other.incs[i]);
      decs[i] = Math.max(decs[i], other.decs[i]);
    }
  }
}
