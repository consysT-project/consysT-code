package de.tuda.stg.consys.demo.triggerchat.schema.datecentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.store.Triggerable;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

public class Group implements Serializable, Triggerable {
    private final List<Ref<@Mutable @Weak User>> users = new LinkedList<>();
    public Group() {}

    @Transactional
    public void postMessage(String msg) {
        for (Ref<@Mutable @Weak User> user : users) {
            user.ref().send(msg);
        }
    }

    public void addUser(Ref<@Mutable @Weak User> user) {
        users.add(user);
    }

    @Override
    public void onTrigger() {
       System.out.println("NEW USER JOINED");
    }
}
