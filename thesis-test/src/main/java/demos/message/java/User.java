package demos.message.java;

import java.io.Serializable;
import java.util.Set;

public class User implements Serializable {

    public final Inbox inbox;
    public final String name;

    public User(Inbox inbox, String name) {
        this.inbox = inbox;
        this.name = name;
    }

    public void send(String msg) {
        inbox.add(msg);
    }

    public Set<String> getInbox() {
        return inbox.getEntries();
    }

    public void printInbox() {
        String s = "[Inbox] " + name + ": " + inbox.toString();
        System.out.println(s);
    }
}
