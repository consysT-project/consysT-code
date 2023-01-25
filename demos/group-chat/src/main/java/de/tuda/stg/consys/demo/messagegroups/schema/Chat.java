package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
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
public class Chat implements Serializable {
    private final List<Ref<@Mutable @Weak User>> users = new LinkedList<>();
    private Counter numOfUsers = new Counter();
    private Ref<@Strong ChatConfig> config;

    public Chat(Ref<@Strong ChatConfig> config) {
        this.config = config;
    }

    @Transactional
    public void postMessage(String msg) {
        for (Ref<@Mutable @Weak User> user : users) {
            user.ref().send(msg);
        }
    }

    @Transactional
    public void addUser(Ref<@Mutable @Weak User> user) {
        if (numOfUsers.getValue() < config.ref().capacity) {
            numOfUsers.inc();
            users.add(user);
        }
    }
}
