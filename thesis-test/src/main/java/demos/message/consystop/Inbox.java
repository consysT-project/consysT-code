package demos.message.consystop;

import org.checkerframework.dataflow.qual.SideEffectFree;
import java.io.Serializable;
import java.util.*;

public class Inbox implements Serializable {

    private final Set<String> entries = new HashSet<>();

    @SideEffectFree
    Set<String> getEntries() {
        return entries;
    }

    void add(String msg) {
        entries.add(msg);
    }

    @Override @SideEffectFree
    public String toString() {
        return "Inbox:" + entries.toString();
    }
}
