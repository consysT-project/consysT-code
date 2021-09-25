package demos.message.java;

import java.io.Serializable;
import java.util.*;

public class Inbox implements Serializable {

    Set<String> entries = new HashSet<>();

    Set<String> getEntries() {
        return entries;
    }

    void add(String msg) {
        entries.add(msg);
    }

    @Override
    public String toString() {
        return "Inbox:" + entries.toString();
    }
}
