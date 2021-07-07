/* There is always a replica who holds the lock */
class DistributedLock {

    /*@
     @ public invariant (\forall int i, j; 0<=i && 0<=j && j<numOfReplicas && i<numOfReplicas;
     @                   lock[i] && lock[j] ==> i == j);
     @ public invariant (\exists int k; k>=0 && k<numOfReplicas; lock[k]);
     @ public invariant timestamp >= 0;
     @*/

    public static final int numOfReplicas = 4;
    public int replicaId;

    boolean[] lock;
    int timestamp;

    /*@
    @ requires id >= 0 && id < numOfReplicas;
    @ ensures lock[0];
    @ ensures (\forall int init; init>=1 && init<numOfReplicas; lock[init] == false);
    @ ensures timestamp == 0;
    @ ensures replicaId == id;
    @*/
    DistributedLock(int id) {
        if (!(id >= 0 && id < numOfReplicas))
            throw new IllegalArgumentException("id not in range.");
        this.replicaId = id;
        this.lock = new boolean[numOfReplicas];
        this.lock[0] = true;
        for(int i = 0; i < numOfReplicas; ++i)
            this.lock[i] = false;
        this.timestamp = 0;
    }

    /*@
    @ requires replicaId >= 0;
    @ requires replicaId < numOfReplicas;
    @ requires lock[replicaId] == true;
    @ requires otherReplica >= 0 && otherReplica < numOfReplicas && otherReplica != replicaId;
    @ assignable timestamp, lock[replicaId], lock[otherReplica];
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures lock[replicaId] == false;
    @ ensures lock[otherReplica] == true;
    @*/
    void transfer(int otherReplica) {
        if (!(lock[replicaId]))
            throw new Exception("The lock is not set to this object.");
        lock[replicaId] = false;
        lock[otherReplica] = true;
        timestamp += 1;
    }

    /*@
    @ requires (timestamp == other.timestamp) ==> (\forall int m0; m0>=0 && m0<numOfReplicas; lock[m0] == other.lock[m0]);
    @ requires lock[replicaId] ==> (timestamp >= other.timestamp);

    @ ensures (other.timestamp < \old(timestamp)) ==> 
                (timestamp == \old(timestamp)) && (\forall int m1; m1>=0 && m1<numOfReplicas; lock[m1] == \old(lock[m1]));
    @ ensures (other.timestamp > \old(timestamp)) ==> 
                (timestamp == other.timestamp) && (\forall int m2; m2>=0 && m2<numOfReplicas; lock[m2] == other.lock[m2]);
    @ ensures (other.timestamp == \old(timestamp)) ==> 
                (timestamp == other.timestamp) && (timestamp == \old(timestamp)) &&
                (\forall int m3; m3>=0 && m3<numOfReplicas; lock[m3] == \old(lock[m3]) && lock[m3] == other.lock[m3]);
    @*/
    void merge(DistributedLock other) {
        if(this.timestamp < other.timestamp) {
            timestamp = other.timestamp;
            for(int i= 0; i < numOfReplicas; ++i)
                lock[i] = other.lock[i];
        }
    }
}
