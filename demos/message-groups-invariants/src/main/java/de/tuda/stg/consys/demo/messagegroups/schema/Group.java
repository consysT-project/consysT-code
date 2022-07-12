package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.invariants.crdts.GMap;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Objects;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class Group implements Serializable {

    private final GMap<Integer, User> users = new GMap();

    public Group() {}

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
    public void addUser(User user) {
        users.put(user.hashCode(), user);
    }

    @WeakOp
    public User getUser(int index) {
        User user = users.get(index);
        Objects.requireNonNull(user, "no user at index " + index);

        return user;
    }
}
