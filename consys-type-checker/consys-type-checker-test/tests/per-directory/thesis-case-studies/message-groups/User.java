package demos.message.consystop;

import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import java.io.*;
import java.util.Set;

public @Mixed class User implements Serializable {

    private final Inbox inbox;
    private final String name;

    public User(@Mutable @Local String name) {
        this.inbox = new Inbox();
        this.name = name;
    }

    @StrongOp
    public void send(String msg) {
        inbox.add(msg);
    }

    public Set<String> getInbox() {
        return inbox.getEntries();
    }

    public void printInbox() {
        @Immutable String s = "[Inbox] " + name + ": " + inbox.toString();
        ((@Mutable PrintStream) System.out).println(s);
    }
}
