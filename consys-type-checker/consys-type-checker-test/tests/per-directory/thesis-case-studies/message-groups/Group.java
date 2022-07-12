package demos.message.consystop;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import java.io.Serializable;
import java.util.*;

public @Mixed class Group implements Serializable {

    private final List<Ref<@Mutable User>> users = new ArrayList<>();

    @Transactional @StrongOp
    public void addPost(String msg) {
        for (@Strong Ref<@Mutable User> user : (@Strong List<@Strong Ref<User>>)users) {
            if (user != null) user.ref().send(msg);
        }
    }

    @StrongOp
    public void addUser(Ref<@Mutable User> user) {
        users.add(user);
    }

    public Ref<User> getUser(int index) {
        Ref<User> user = users.get(index);
        Objects.requireNonNull(user, "no user at index " + index);

        return user;
    }
}
