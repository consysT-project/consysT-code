package de.tuda.stg.consys.demo.groupchat.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
public class Chat implements Serializable {
    private Ref<@Mutable @Weak Inbox> inbox;
    private Ref<@Mutable @Strong Counter> numOfUsers;
    private Ref<@Mutable @Strong ChatConfig> config;

    public Chat(Ref<@Mutable @Weak Inbox> inbox, Ref<@Mutable @Strong Counter> numOfUsers,  Ref<@Mutable @Strong ChatConfig> config) {
        this.inbox = inbox;
        this.numOfUsers = numOfUsers;
        this.config = config;
    }

    @Transactional
    public Ref<@Mutable @Weak Inbox> registerUser(Ref<@Mutable @Weak User> user) {
        if (numOfUsers.ref().getValue() < config.ref().capacity) {
            numOfUsers.ref().inc();
            return inbox;
        }
        return null;
    }
}
