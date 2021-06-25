class Consensus {

  //@ public invariant flag ==> (\forall int i; i >= 0 && i < numOfReplicas; b[i]);
  
  public static final int numOfReplicas = 10;

  /* Indicates that consensus has been found */
  boolean flag;
  /* Indicates the votes from all replicas */
  boolean[] b;
  int replicaId = 4;

  /*@
  @ requires id >= 0 && id < numOfReplicas;
  @ ensures flag == false;
  @ ensures (\forall int i2; i2 >= 0 && i2 < numOfReplicas; b[i2] == false);
  @*/
  public Consensus(int id) {
    flag = false;
    b = new boolean[numOfReplicas];
  }

  /*@
  @ assignable \nothing;
  @ ensures \result == (\forall int i3; i3 >= 0 && i3 < numOfReplicas; b[i3]);
  @*/
  boolean conjunctValues() { return false;}

  /*@
  @ assignable b[replicaId];
  @ ensures b[replicaId];
  @ ensures (\forall int i4; i4 >= 0 && i4 < numOfReplicas && i4 != replicaId;
              b[i4] == \old(b[i4]));
  @*/
  void mark() {}

  /*@
  @ requires (\forall int i5; i5 >= 0 && i5 < numOfReplicas; b[i5]);
  @ assignable flag;
  @ ensures flag;
  @*/
  void agree() {}

  /*@
  @ ensures flag == (\old(flag) || other.flag);
  @ ensures (\forall int i6; i6>=0 && i6<numOfReplicas;
              b[i6] == (\old(b[i6]) || other.b[i6]));
  @*/
  void merge(Consensus other) {}
}
