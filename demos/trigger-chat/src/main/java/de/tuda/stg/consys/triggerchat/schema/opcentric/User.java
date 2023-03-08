package de.tuda.stg.consys.triggerchat.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

public @Mixed class User implements Serializable {
    private @Immutable String name;
    private Ref<@Mutable @Weak Inbox> inbox;
    public User() {}
    public User(@Local String name, Ref<@Mutable @Weak Inbox> inbox) {
        this.name = name;
        this.inbox = inbox;
    }

    @Transactional
    public void send(String msg) {
        inbox.ref().send(msg);
    }

}