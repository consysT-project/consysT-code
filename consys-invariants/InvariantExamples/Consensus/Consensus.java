class Consensus {

  //@ public invariant flag ==> conjunctValues();
  
  public static final int numOfReplicas = 10;
  public static final int replicaId = 4;

  /* Indicates that consensus has been found */
  boolean flag;
  /* Indicates the votes from all replicas */
  boolean[] b;

  /*@
  @ ensures flag == false;
  @ ensures (\forall int init; init>=0 && init<numOfReplicas; b[init] == false);
  @*/
  public Consensus() {}

  /*@
  @ assignable \nothing;
  @ ensures \result == (\forall int con; con>=0 && con<numOfReplicas; b[con]);
  @*/
  boolean conjunctValues() { return false;}

  /*@
  @ ensures b[replicaId] && (flag == \old(flag));
  @ ensures (\forall int j; j>=0 && j<numOfReplicas && j!=replicaId;
              b[j] == \old(b[j]));
  @*/
  void mark() {}

  /*@
  @ requires \old(conjunctValues());
  @ ensures flag && (\forall int index; index>=0 && index<numOfReplicas;
                        b[index] == \old(b[index]));
  @*/
  void agree() {}

  /*@
  @ ensures flag == (\old(flag) || other.flag);
  @ ensures (\forall int mergeIndex; mergeIndex>=0 && mergeIndex<numOfReplicas;
              b[mergeIndex] == (\old(b[mergeIndex]) || other.b[mergeIndex]));
  @*/
  void merge(Consensus other) {}
}
