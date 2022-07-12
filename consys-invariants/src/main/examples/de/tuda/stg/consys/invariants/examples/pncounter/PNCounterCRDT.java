package de.tuda.stg.consys.invariants.examples.pncounter;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.utils.InvariantUtils.replicaId;

@ReplicatedModel public class PNCounterCRDT {

  //@ public invariant (\forall int i; i >= 0 && i < numOfReplicas(); incs[i] >= 0 && decs[i] >= 0);

    public int[] incs;
    public int[] decs;

  /* Constructors */
  // Constructors define the initial state of an object.
  //@ ensures (\forall int i; i >= 0 && i < numOfReplicas(); incs[i] == 0 && decs[i] == 0);
  public PNCounterCRDT() {
    this.incs = new int[numOfReplicas()];
    this.decs = new int[numOfReplicas()];
  }


  /*@
  @ assignable \nothing;
  @ ensures \result ==
            (\sum int incInd; incInd>=0 && incInd<numOfReplicas(); incs[incInd]);
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
            (\sum int decInd; decInd>=0 && decInd<numOfReplicas(); decs[decInd]);
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
  public int getValue() { return sumIncs() - sumDecs(); }



  /*@
  @ assignable incs[replicaId()];
  @ ensures incs[replicaId()] == \old(incs[replicaId()]) + 1;
  @*/
  public Void inc() {
    incs[replicaId()] = incs[replicaId()] + 1;
    return null;
  }

  /*@
  @ requires n >= 0;
  @ assignable incs[replicaId()];
  @ ensures incs[replicaId()] == \old(incs[replicaId()]) + n;
  @*/
  public Void inc(int n) {
    incs[replicaId()] = incs[replicaId()] + n;
    return null;
  }

  /*@
  @ assignable decs[replicaId()];
  @ ensures decs[replicaId()] == \old(decs[replicaId()]) + 1;
  @*/
  public Void dec() {
    if (1 > getValue())
      throw new IllegalArgumentException("not enough balance to withdraw");
    decs[replicaId()] = decs[replicaId()] + 1;
    return null;
  }

  /*@
  @ requires n >= 0;
  @ assignable decs[replicaId()];
  @ ensures decs[replicaId()] == \old(decs[replicaId()]) + n;
  @*/
  public Void dec(int n) {
    if (n > getValue())
      throw new IllegalArgumentException("not enough balance to withdraw");
    decs[replicaId()] = decs[replicaId()] + n;
    return null;
  }

  /*@
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas();
                   (\old(incs[i]) >= other.incs[i] ? incs[i] == \old(incs[i]) : incs[i] == other.incs[i])
                && (\old(decs[i]) >= other.decs[i] ? decs[i] == \old(decs[i]) : decs[i] == other.decs[i]));
    @ ensures replicaId() == \old(replicaId());
  @*/
  public Void merge(PNCounterCRDT other) {
    for (int i = 0; i < numOfReplicas(); i++) {
      incs[i] = Math.max(incs[i], other.incs[i]);
      decs[i] = Math.max(decs[i], other.decs[i]);
    }

    return null;
  }
}
