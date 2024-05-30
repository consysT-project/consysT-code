package de.tuda.stg.consys.demo.messagegroups.op.schema;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.invariants.lib.crdts.GCounter;
import de.tuda.stg.consys.invariants.lib.crdts.GMap;

import java.io.Serializable;
import java.util.Objects;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class Group implements Serializable, Mergeable<Group> {

    private final GCounter counter = new GCounter();

    private final GMap<Integer, User> users = new GMap();

    // invariant number of users == counter value
    // counter value < 100

    public Group() {

    }

    //Message delivery
    @WeakOp
    @Transactional
    public void addPost(String msg) {
        for (User user : users.underlying.values()) {
            if (user != null) user.send(msg);
        }
    }

    //Join group
    @StrongOp
    public int addUser(User user) {
        if (counter.getValue() < 100) {
            counter.inc();
            users.put(counter.getValue(), user);
        }

        return counter.getValue();
    }

    @WeakOp
    public User getUser(int index) {
        User user = users.get(index);
        Objects.requireNonNull(user, "no user at index " + index);

        return user;
    }

    @Override
    public Void merge(Group other) {
        counter.merge(other.counter);
        users.merge(other.users);
        return null;
    }
}
