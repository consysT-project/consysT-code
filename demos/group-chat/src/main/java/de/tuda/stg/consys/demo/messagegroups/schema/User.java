package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.List;


/**
 * message delivery (Figure 4), user creation, inbox checking, and group joining
 *
 * @author Mirko Köhler
 */
public class User implements Serializable {
    private final @Immutable String name;
    private final Ref<@Mutable @Weak Inbox> inbox;


    public User(@Local String name, Ref<@Mutable @Weak Inbox> inbox) {
        this.name = name;
        this.inbox = inbox;
    }

    @Transactional
    public void send(String msg) {
        inbox.ref().add(msg);
    }
}
