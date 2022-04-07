package de.tuda.stg.consys.demo.messagegroups.schema;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class Inbox implements Serializable {

    private final Set<String> entries = new HashSet<>();

    public Inbox() {}

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
