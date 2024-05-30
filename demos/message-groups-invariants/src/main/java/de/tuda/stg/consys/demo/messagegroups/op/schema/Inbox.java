package de.tuda.stg.consys.demo.messagegroups.op.schema;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.invariants.lib.crdts.GSet;


import java.io.Serializable;
import java.util.Set;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class Inbox implements Serializable, Mergeable<Inbox> {

    private final GSet<String> entries = new GSet<>();

    public Inbox() {}

    public Set<String> getEntries() {
        return entries.getValue();
    }

    public void add(String msg) {
        entries.add(msg);
    }

    @Override
    public String toString() {
        return "Inbox:" + entries.toString();
    }

    @Override
    public Void merge(Inbox other) {
        return entries.merge(other.entries);
    }
}
