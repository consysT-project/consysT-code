package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
public @Mixed class Group implements Serializable {
    private final List<Ref<@Mutable User>> users = new LinkedList<>();

    private int capacity = 100;

    @Transactional
    public void postMessage(String msg) {
        for (Ref<@Mutable User> user : users) {
            user.ref().send(msg);
        }
    }

    @StrongOp
    public void addUser(Ref<@Mutable User> user) {
        if (users.size() < capacity)
            users.add(user);
        else
            throw new IllegalArgumentException("no space for users");
    }

    @StrongOp
    public void setCapacity(@Strong int capacity) {
        this.capacity = capacity;
    }

    @SideEffectFree
    public int getCapacity() {
        return capacity;
    }

    @SideEffectFree
    public List<Ref<@Mutable User>> getUsers() {
        return users;
    }
}
