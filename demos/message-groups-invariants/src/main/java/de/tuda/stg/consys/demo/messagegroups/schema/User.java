package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.WeakOp;

import java.io.Serializable;
import java.util.Set;


/**
 * message delivery (Figure 4), user creation, inbox checking, and group joining
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class User implements Serializable, Mergeable<User> {

    private final Inbox inbox;
    private final String name;

    public User() {
        inbox = null;
        name = "";
    }

    public User(Inbox inbox, String name) {
        this.inbox = inbox;
        this.name = name;
    }

    @WeakOp
    @Transactional
    public void send(String msg) {
//		System.out.println("[Message] " + name + ": " + msg);
        inbox.add(msg);
    }

    @WeakOp
    @Transactional
    public Set<String> getInbox() {
        return inbox.getEntries();
    }

    @WeakOp
    @Transactional
    public void printInbox() {
        String s = "[Inbox] " + name + ": " + inbox.toString();
        System.out.println(s);
    }

    @Override
    public Void merge(User other) {
        inbox.merge(other.inbox);
        return null;
    }
}
