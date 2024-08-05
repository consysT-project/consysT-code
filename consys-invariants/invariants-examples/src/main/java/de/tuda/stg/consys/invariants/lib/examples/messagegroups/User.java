package de.tuda.stg.consys.invariants.lib.examples.messagegroups;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;

import java.io.Serializable;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;


/**
 * message delivery (Figure 4), user creation, inbox checking, and group joining
 *
 * @author Mirko Köhler
 */
@ReplicatedModel
public class User implements Serializable, Mergeable<User> {
    private final Inbox inbox;
    private final String name;

    static { /* Prevent IntelliJ from removing the import */ stateful(null); }

    //@ ensures this.name == name;
    //@ ensures inbox.entries.isEmpty();
    public User(String name) {
        inbox = new Inbox();
        this.name = name;
    }

    //@ assignable inbox;
    //@ ensures stateful(inbox.add(msg));
    @WeakOp  public Void send(String msg) {
        /* Weak */
        inbox.add(msg);
        return null;
    }

    //@ ensures stateful(inbox.merge(other.inbox));
    @Override
    public Void merge(User other) {
        inbox.merge(other.inbox);
        return null;
    }
}
