package demos.message.consyst;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import java.io.Serializable;
import java.util.*;

public @Strong class Group implements Serializable {

    private final List<Ref<User>> users = new ArrayList<>();

    @Transactional
    public void addPost(String msg) {
        for (@Weak Ref<User> user : (@Strong List<@Weak Ref<User>>) users) {
            if (user != null) user.ref().send(msg);
        }
    }

    public void addUser(Ref<User> user) {
        users.add(user);
    }

    public Ref<User> getUser(int index) {
        Ref<User> user = users.get(index);
        Objects.requireNonNull(user, "no user at index " + index);

        return user;
    }
}
