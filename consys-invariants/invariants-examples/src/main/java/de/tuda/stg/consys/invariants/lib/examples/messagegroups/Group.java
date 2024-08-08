package de.tuda.stg.consys.invariants.lib.examples.messagegroups;


import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;

import java.io.Serializable;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;


@ReplicatedModel public class Group implements Mergeable<Group>, Serializable {

    public static final int MAX_USERS = 3;
    public static final int MAX_USER_ID = 5;

    public int[] counter;
    public Map<Integer, Set<String>> inboxes;

    static { stateful(null); }

    //@ public invariant (\sum int i; i >= 0 && i < numOfReplicas(); counter[i]) >= 0;
    //@ public invariant (\sum int i; i >= 0 && i < numOfReplicas(); counter[i]) <= 3;
    //@ public invariant (\forall int uid; uid >= 5; inboxes.get(uid).isEmpty());

    //@ public invariant getCounterValue() == getUserCount();

    //@ ensures (\forall int i; ; counter[i] == 0);
    //@ ensures (\forall int uid; ; inboxes.get(uid).isEmpty());
    public Group() {
        this.counter = new int[numOfReplicas()];
        this.inboxes = new HashMap<>();
    }

    //@ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); counter[i]);
    public int getCounterValue() {
        int result = 0;
        for (int i=0; i<numOfReplicas(); i++) result += counter[i];
        return result;
    }

    //@ ensures \result == (\sum int uid; uid >= 0 && uid < 5; inboxes.get(uid).isEmpty() ? 0 : 1);
    public int getUserCount() {
        int result = 0;
        for (Set<String> inbox : inboxes.values()) if (!inbox.isEmpty()) result++;
        return result;
    }

    //@ requires uid >= 0 && uid < 5;
    //@ requires getCounterValue() < 3;
    //@ ensures (!\old(inboxes).get(uid).isEmpty()) ? (counter == \old(counter)) : (counter[replicaId()] == \old(counter)[replicaId()] + 1);
    //@ ensures inboxes.get(uid).containsAll(inbox);
    //@ ensures inboxes.get(uid).contains("Welcome to the group!");
    //@ ensures (\forall int otherUser; ; inboxes.get(otherUser) == \old(inboxes).get(otherUser) || otherUser != uid);
    public Void addUser(Integer uid, Set<String> inbox) {
        /* Strong */
        if (uid < 0 || uid >= MAX_USER_ID) {
            throw new IllegalArgumentException("UserID is not in the expected range");
        }
        if (getCounterValue() >= MAX_USERS) {
            throw new RuntimeException("Cannot add user: group is already full");
        }
        if (inboxes.containsKey(uid)) {
            inboxes.get(uid).addAll(inbox);
        } else {
            counter[replicaId()] += 1;
            var newInbox = new HashSet<String>();
            newInbox.add("Welcome to the group!");
            newInbox.addAll(inbox);
            inboxes.put(uid, newInbox);
        }
        return null;
    }

    //@ requires uid >= 0 && uid < 5;
    //@ ensures inboxes.get(uid).containsAll(\old(inboxes).get(uid));
    //@ ensures inboxes.get(uid).containsAll(other.inboxes.get(uid));
    //@ ensures (\forall String msg; inboxes.get(uid).contains(msg); \old(inboxes).get(uid).contains(msg) || other.inboxes.get(uid).contains(msg));
    //@ ensures (\forall int otherUser; ; inboxes.get(otherUser) == \old(inboxes).get(otherUser) || otherUser == uid);
    private Void mergeUserInbox(Integer uid, Group other) {
        if (other.inboxes.containsKey(uid)) {
            var otherInbox = other.inboxes.get(uid);
            if (inboxes.containsKey(uid)) inboxes.get(uid).addAll(otherInbox);
            else inboxes.put(uid, otherInbox);
        }
        return null;
    }

    //@ ensures (\forall int uid; !\old(inboxes).get(uid).isEmpty(); inboxes.get(uid).contains(message));
    public Void postMessage(String message) {
        /* Weak */
        for (var inbox : inboxes.values()) if (!inbox.isEmpty()) inbox.add(message);
        return null;
    }

    //@ ensures (\forall int i; ; counter[i] == Math.max(\old(counter[i]), other.counter[i]));
    //@ ensures (\forall int u; ; inboxes.get(u).containsAll(\old(inboxes).get(u)));
    //@ ensures (\forall int u; ; inboxes.get(u).containsAll(other.inboxes.get(u)));
    //@ ensures (\forall int u; ; (\forall String msg; inboxes.get(u).contains(msg); \old(inboxes).get(u).contains(msg) || other.inboxes.get(u).contains(msg)));
    //@ ensures (\forall int u; !inboxes.get(u).isEmpty() ; stateful(mergeUserInbox(u, other)));
    //@ ensures (\forall int u; !other.inboxes.get(u).isEmpty(); stateful(addUser(u, other.inboxes.get(u))));
    public Void merge(Group other) {
        for (int i=0; i<numOfReplicas(); i++) counter[i] = Math.max(counter[i], other.counter[i]);
        for (var user : inboxes.keySet()) mergeUserInbox(user, other);
        for (var otherUser : other.inboxes.entrySet()) if (!otherUser.getValue().isEmpty()) addUser(otherUser.getKey(), otherUser.getValue());
        return null;
    }
}