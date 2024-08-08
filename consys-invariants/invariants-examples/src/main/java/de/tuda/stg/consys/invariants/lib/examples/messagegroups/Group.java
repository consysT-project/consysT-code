package de.tuda.stg.consys.invariants.lib.examples.messagegroups;


import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;

import de.tuda.stg.consys.annotations.invariants.ArrayUtils;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.HashSet;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;

@ReplicatedModel public class Group implements Mergeable<Group>, Serializable {

    public int[] counter;
    public Map<Integer, Set<String>> inboxes;

    //@ public invariant (\sum int i; i >= 0 && i < numOfReplicas(); counter[i]) >= 0;
    //@ public invariant (\sum int i; i >= 0 && i < numOfReplicas(); counter[i]) <= 3;
    //@ public invariant (\forall int uid; uid >= 5; inboxes.get(uid).isEmpty());

    //@ public invariant (\sum int uid; uid >= 0 && uid < 5; inboxes.get(uid).isEmpty() ? 0 : 1) == (\sum int i; i >= 0 && i < numOfReplicas(); counter[i]);

    //@ ensures (\forall int i; ; counter[i] == 0);
    //@ ensures (\forall int uid; ; inboxes.get(uid).isEmpty());
    public Group() {
        this.counter = new int[numOfReplicas()];
        this.inboxes = new HashMap<>();
    }

    //@ requires uid >= 0 && uid < 5;
    //@ requires (\sum int i; i >= 0 && i < numOfReplicas(); counter[i]) < 3;
    //@ ensures (!\old(inboxes).get(uid).isEmpty()) ? (counter == \old(counter)) : (counter[replicaId()] == \old(counter)[replicaId()] + 1);
    //@ ensures inboxes.get(uid).containsAll(inbox);
    //@ ensures inboxes.get(uid).contains("welcome to the group");
    //@ ensures (\forall int otherUser; ; inboxes.get(otherUser) == \old(inboxes).get(otherUser) || otherUser != uid);
    public Void addUser(Integer uid, Set<String> inbox) {
        // TODO fill
        return null;
    }

    //@ requires uid >= 0 && uid < 5;
    //@ ensures inboxes.get(uid).containsAll(\old(inboxes).get(uid));
    //@ ensures inboxes.get(uid).containsAll(other.inboxes.get(uid));
    //@ ensures (\forall String msg; inboxes.get(uid).contains(msg); \old(inboxes).get(uid).contains(msg) || other.inboxes.get(uid).contains(msg));
    //@ ensures (\forall int otherUser; ; inboxes.get(otherUser) == \old(inboxes).get(otherUser) || otherUser == uid);
    public Void mergeUserInbox(Integer uid, Group other) {
        return null;
    }

    //@ ensures (\forall int uid; !\old(inboxes).get(uid).isEmpty(); inboxes.get(uid).contains(message));
    public Void postMessage(String message) {
        return null;
    }

    //@ ensures (\forall int i; ; counter[i] == Math.max(\old(counter[i]), other.counter[i]));
    //@ ensures (\forall int u; ; inboxes.get(u).containsAll(\old(inboxes).get(u)));
    //@ ensures (\forall int u; ; inboxes.get(u).containsAll(other.inboxes.get(u)));
    //@ ensures (\forall int u; ; (\forall String msg; inboxes.get(u).contains(msg); \old(inboxes).get(u).contains(msg) || other.inboxes.get(u).contains(msg)));
    //@ ensures (\forall int u; ; stateful(mergeUserInbox(u, other)));
    //@ ensures (\forall int u; !other.inboxes.get(u).isEmpty(); stateful(addUser(u, other.inboxes.get(u))));
    public Void merge(Group other) {
        // TODO fill
        return null;
    }
}