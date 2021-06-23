/* There is always a replica who holds the lock */
class DistributedLock {

    /*@
     @ public invariant (\forall int i, j; 0<=i && 0<=j && j<numOfReplicas && i<numOfReplicas;
     @                   lock[i] && lock[j] ==> i == j);
     @ public invariant (\exists int k; k>=0 && k<numOfReplicas; lock[k]);
     @*/

    final int numOfReplicas = 10;
    final int replicaId = 3;

    boolean[] lock;
    int timestamp;

    /*@
    @ ensures lock[0];
    @ ensures lock.length == 10;
    @ ensures (\forall int init; init>=1 && init<numOfReplicas; lock[init] == false);
    @ ensures timestamp == 0;
    @*/
    DistributedLock() {}

    /*@
    @ requires lock[replicaId] == true;
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures lock[replicaId] == false;
    @ ensures lock[otherReplica] == true;
    @ ensures (\forall int transInd; transInd>=0 && transInd<numOfReplicas &&
                transInd!=replicaId && transInd!=otherReplica; lock[transInd] == \old(lock[transInd]));
    @*/
    void transfer(int otherReplica) {}

    /*@
    @ requires (\old(timestamp) == other.timestamp) ==> (\forall int m0; m0>=0 && m0<NumOfReplicas; \old(lock[m0])==other.lock[m0]);
    @ requires \old(lock[replicaId]) ==> (\old(timestamp) >= other.timestamp);

    @ ensures (other.timestamp < \old(timestamp)) ==> 
                (timestamp == \old(timestamp)) && (\forall int m1; m1>=0 && m1<numOfReplicas; lock[m1] == \old(lock[m1]));
    @ ensures (other.timestamp > \old(timestamp)) ==> 
                (timestamp == other.timestamp) && (\forall int m2; m2>=0 && m2<numOfReplicas; lock[m2] == other.lock[m2]);
    @ ensures (other.timestamp == \old(timestamp)) ==> 
                (timestamp == other.timestamp) && (timestamp == \old(timestamp)) &&
                (\forall int m3; m3>=0 && m3<numOfReplicas; lock[m3] == \old(lock[m3]) && lock[m3] == other.lock[m3]);
    @*/
    void merge(DistributedLock other) {}
}
