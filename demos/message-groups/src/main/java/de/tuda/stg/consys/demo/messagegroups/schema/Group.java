package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Objects;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
public class Group implements Serializable {

    private final Ref<User>[] users = new Ref[100];

    //Message delivery
    @WeakOp
    @Transactional
    public void addPost(String msg) {
        for (Ref<User> user : users) {
            if (user != null) user.ref().send(msg);
        }
    }

    //Join group
    @StrongOp
    public void addUser(Ref<User> user) {
        for (int i = 0; i < users.length; i++) {
            if (users[i] == null) {
                users[i] = user;
                return;
            }
        }
        throw new IllegalArgumentException("no space for users");
    }

    @WeakOp
    public Ref<User> getUser(int index) {
        Ref<User> user = users[index];
        Objects.requireNonNull(user, "no user at index " + index);

        return user;
    }
}
