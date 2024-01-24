package de.tuda.stg.consys.invariants.lib.examples.consensus;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;


@ReplicatedModel public class Consensus implements Mergeable<Consensus>, Serializable {



  /* Indicates that consensus has been found */
  boolean flag;
  /* Indicates the votes from all replicas */
  boolean[] b;
  int replicaId;

  //@ public invariant flag ==> (\forall int i; i >= 0 && i < numOfReplicas(); b[i]);



  //@ requires id >= 0 && id < numOfReplicas();
  //@ ensures flag == false;
  //@ ensures (\forall int i; i >= 0 && i < numOfReplicas(); b[i] == false);
  //@ ensures replicaId == id;
  public Consensus(int id) {
    if (!(id >= 0 && id < numOfReplicas()))
      throw new IllegalArgumentException("id not in range.");
    flag = false;
    replicaId = id;
    b = new boolean[numOfReplicas()];
    for(int i = 0; i < numOfReplicas(); ++i)
      b[i] = false;
  }

  public Consensus() {
    this(replicaId());
  }

  /*@
  @ assignable \nothing;
  @ ensures \result == (\forall int i; i >= 0 && i < numOfReplicas(); b[i]);
  @*/
  
   public boolean conjunctValues() {
    for(int i = 0; i < numOfReplicas(); ++i) {
      if (!b[i])
        return false;
    }
    return true;
  }

  /*@
  @ assignable b[replicaId];
  @ ensures b[replicaId];
  @ ensures (\forall int i; i >= 0 && i < numOfReplicas() && i != replicaId;
              b[i] == \old(b[i]));
  @*/
   public void mark() {
    b[replicaId] = true;
  }

  /*@
  @ requires (\forall int i; i >= 0 && i < numOfReplicas(); b[i]);
  @ assignable flag;
  @ ensures flag;
  @*/
   public void agree() {
    if (!conjunctValues())
      throw new RuntimeException("There is still a false element.");
    flag = true;
  }

  /*@
  @ ensures flag == (\old(flag) | other.flag);
  @ ensures (\forall int i; i >= 0 && i < numOfReplicas();
              b[i] == (\old(b[i]) | other.b[i]));
  @*/
  public Void merge(Consensus other) {
    for(int i = 0; i < numOfReplicas(); ++i)
      b[i] = b[i] | other.b[i];
    flag = flag | other.flag;
    return null;
  }
}
