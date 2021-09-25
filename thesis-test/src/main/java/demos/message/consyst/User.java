package demos.message.consyst;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import java.io.Serializable;
import java.util.Set;

public @Weak class User implements Serializable {

    private final Ref<Inbox> inbox;
    private final String name;

    public User(Ref<Inbox> inbox, @Weak String name) {
        this.inbox = inbox;
        this.name = name;
    }

    @Transactional
    public void send(String msg) {
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
