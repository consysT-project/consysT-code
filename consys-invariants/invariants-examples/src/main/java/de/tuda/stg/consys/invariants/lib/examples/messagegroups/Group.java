package de.tuda.stg.consys.invariants.lib.examples.messagegroups;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.invariants.lib.crdts.GCounter;
import de.tuda.stg.consys.invariants.lib.crdts.GSet;

import java.io.Serializable;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
@ReplicatedModel
public class Group implements Serializable, Mergeable<Group> {
    /* invariant: number of users is max 100 */
    private final GCounter counter = new GCounter();
    private final UserGSet users = new UserGSet();

    static { /* Prevent IntelliJ from removing the import */ stateful(null); }

    //@ public invariant counter.getValue() >= 0 && counter.getValue() <= 100;

    //@ ensures counter.getValue() == 0;
    //@ ensures users.isEmpty();
    public Group() {}

    //@ assignable \nothing;
    //@ ensures (\forall User user; users.contains(user); stateful(user.send(msg)));
    @WeakOp  public Void addPost(String msg) {
        /* Weak */
        for (User user : users.getValue()) {
            if (user != null) user.send(msg);
        }
        return null;
    }

    //@ requires counter.getValue() < 100;
    //@ ensures stateful(counter.inc());
    //@ ensures users.contains(user);
    @StrongOp  public Void addUser(User user) {
        /* Strong */
        if (counter.getValue() >= 100)
            throw new IllegalArgumentException();
        counter.inc();
        users.add(user);
        return null;
    }

    //@ requires (\forall User user; \old(users).contains(user) || other.users.contains(user); user.contains(user));
    //@ ensures stateful(counter.merge(other.counter));
    //@ ensures stateful(users.merge(other.users));
    @Override
    public Void merge(Group other) {
        counter.merge(other.counter);
        users.merge(other.users);
        return null;
    }
}
