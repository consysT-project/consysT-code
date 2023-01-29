package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.List;


/**
 * message delivery (Figure 4), user creation, inbox checking, and group joining
 *
 * @author Mirko Köhler
 */
public @Mixed class User implements Serializable {
    private final @Immutable String name;
    private final Ref<@Mutable Inbox> inbox;

    // empty constructor needed for mixed objects
    public User() {
        inbox = null;
        name = "";
    }

    public User(@Local String name, Ref<@Mutable Inbox> inbox) {
        this.name = name;
        this.inbox = inbox;
    }

    @Transactional
    public void send(String msg) {
        inbox.ref().add(msg);
    }

    @Transactional
    @SideEffectFree
    public List<String> getInbox() {
        return inbox.ref().getEntries();
    }

    @Transactional
    @SideEffectFree
    public void printInbox() {
        @Immutable String s = "[Inbox] " + name + ": " + inbox.ref().toString();
        System.out.println(s);
    }
}
