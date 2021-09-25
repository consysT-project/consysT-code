package demos.message.consyst;

import de.tuda.stg.consys.checker.qual.*;
import java.io.Serializable;
import java.util.*;

public @Strong class Inbox implements Serializable {

    Set<String> entries = new HashSet<>();

    public Set<String> getEntries() {
        return entries;
    }

    public void add(String msg) {
        entries.add(msg);
    }

    @Override
    public String toString() {
        return "Inbox:" + entries.toString();
    }
}
