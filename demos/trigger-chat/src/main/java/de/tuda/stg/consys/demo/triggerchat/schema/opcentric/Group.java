package de.tuda.stg.consys.demo.triggerchat.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.core.store.Triggerable;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

public @Mixed class Group implements Serializable, Triggerable {
    private final List<Ref<@Mutable @Weak User>> users = new LinkedList<>();
    public Group() {}

    @Transactional @WeakOp
    public void postMessage(String msg) {
        for (Ref<@Mutable @Weak User> user : users) {
            user.ref().send(msg);
        }
    }

    @StrongOp
    public void addUser(Ref<@Mutable @Weak User> user) {
        users.add(user);
    }

    @Override
    public void onTrigger() {
        System.out.println("NEW USER JOINED");
    }
}
