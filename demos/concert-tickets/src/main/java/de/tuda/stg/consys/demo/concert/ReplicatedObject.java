package de.tuda.stg.consys.demo.concert;

import akka.actor.ActorRef;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicatedObject;
import de.tuda.stg.consys.core.legacy.akka.Requests;
import de.tuda.stg.consys.japi.legacy.JRef;
import scala.collection.mutable.Buffer;


//The code is commented out because of accessibility issues.
public class ReplicatedObject<T> {
    final AkkaReplicatedObject<String, T> internal;
    final AkkaReplicaSystem system;
    final Buffer<Requests.Operation<?>> localOperations;
    final String address;
    final ActorRef master;

    final boolean isMaster;
    final boolean isFollower;

    private ReplicatedObject(AkkaReplicatedObject<String, T> internal) {
        this.internal = internal;
//        if (internal instanceof StrongAkkaReplicaSystem$StrongReplicatedObject$StrongFollowerReplicatedObject) {
//            StrongAkkaReplicaSystem$StrongReplicatedObject$StrongFollowerReplicatedObject<String, T> obj =
//                    (StrongAkkaReplicaSystem$StrongReplicatedObject$StrongFollowerReplicatedObject<String, T>) internal;
//            this.system = obj.replicaSystem();
//            this.address = obj.addr();
//            this.master = obj.masterReplica();
//            this.localOperations = null;
//            this.isMaster = false;
//            this.isFollower = true;
//        }
//        else if (internal instanceof WeakAkkaReplicaSystem$WeakReplicatedObject$WeakFollowerReplicatedObject) {
//            WeakAkkaReplicaSystem$WeakReplicatedObject$WeakFollowerReplicatedObject<String, T> obj =
//                    (WeakAkkaReplicaSystem$WeakReplicatedObject$WeakFollowerReplicatedObject<String, T>) internal;
//            this.system = obj.replicaSystem();
//            this.address = obj.addr();
//            this.master = obj.masterReplica();
//            this.localOperations = obj.unsynchronized();
//            this.isMaster = false;
//            this.isFollower = true;
//        }
//        else if (internal instanceof StrongAkkaReplicaSystem$StrongReplicatedObject$StrongMasterReplicatedObject) {
//            StrongAkkaReplicaSystem$StrongReplicatedObject$StrongMasterReplicatedObject<String, T> obj =
//                    (StrongAkkaReplicaSystem$StrongReplicatedObject$StrongMasterReplicatedObject<String, T>) internal;
//            this.system = obj.replicaSystem();
//            this.address = obj.addr();
//            this.master = null;
//            this.localOperations = null;
//            this.isMaster = true;
//            this.isFollower = false;
//        }
//        else if (internal instanceof WeakAkkaReplicaSystem$WeakReplicatedObject$WeakMasterReplicatedObject) {
//            WeakAkkaReplicaSystem$WeakReplicatedObject$WeakMasterReplicatedObject<String, T> obj =
//                    (WeakAkkaReplicaSystem$WeakReplicatedObject$WeakMasterReplicatedObject<String, T>) internal;
//            this.system = obj.replicaSystem();
//            this.address = obj.addr();
//            this.master = null;
//            this.localOperations = null;
//            this.isMaster = true;
//            this.isFollower = false;
//        }
//        else {
            this.system = null;
            this.master = null;
            this.localOperations = null;
            this.address = null;
            this.isMaster = false;
            this.isFollower = false;
//        }
    }

    public static <T> ReplicatedObject<T> from(JRef<T> ref) {
//        return new ReplicatedObject<T>((AkkaReplicatedObject<String, T>) ((JRefImpl<T>) ref).getRef().deref());
        return null;
    }
}
