class Consensus {

  public static final int numOfReplicas = 10;

  /* Indicates that consensus has been found */
  boolean flag;
  /* Indicates the votes from all replicas */
  boolean[] b;
  int replicaId = 4;

  //@ public invariant flag ==> (\forall int i; i >= 0 && i < numOfReplicas; b[i]);


  /*@
  @ requires id >= 0 && id < numOfReplicas;
  @ ensures flag == false;
  @ ensures (\forall int i; i >= 0 && i < numOfReplicas; b[i] == false);
  @*/
  public Consensus(int id) {
    flag = false;
    b = new boolean[numOfReplicas];
  }

  /*@
  @ assignable \nothing;
  @ ensures \result == (\forall int i; i >= 0 && i < numOfReplicas; b[i]);
  @*/
  boolean conjunctValues() { return false;}

  /*@
  @ assignable b[replicaId];
  @ ensures b[replicaId];
  @ ensures (\forall int i; i >= 0 && i < numOfReplicas && i != replicaId;
              b[i] == \old(b[i]));
  @*/
  void mark() {}

  /*@
  @ requires (\forall int i; i >= 0 && i < numOfReplicas; b[i]);
  @ assignable flag;
  @ ensures flag;
  @*/
  void agree() {}

  /*@
  @ ensures flag == (\old(flag) || other.flag);
  @ ensures (\forall int i; i >= 0 && i < numOfReplicas;
              b[i] == (\old(b[i]) || other.b[i]));
  @*/
  void merge(Consensus other) {}
}
