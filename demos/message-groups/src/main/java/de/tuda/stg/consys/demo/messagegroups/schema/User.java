package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Set;


/**
 * message delivery (Figure 4), user creation, inbox checking, and group joining
 *
 * @author Mirko Köhler
 */
public class User implements Serializable {

    private final Ref<Inbox> inbox;
    private final String name;

    public User(Ref<Inbox> inbox, String name) {
        this.inbox = inbox;
        this.name = name;
    }

    @Transactional
    public void send(String msg) {
//		System.out.println("[Message] " + name + ": " + msg);
        inbox.ref().add(msg);
    }

    @Transactional
    public Set<String> getInbox() {
        return inbox.ref().getEntries();
    }

    @Transactional
    public void printInbox() {
        String s = "[Inbox] " + name + ": " + inbox.ref().toString();
        System.out.println(s);
    }
}
