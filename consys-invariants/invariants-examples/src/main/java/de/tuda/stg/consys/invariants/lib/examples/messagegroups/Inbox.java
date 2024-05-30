package de.tuda.stg.consys.invariants.lib.examples.messagegroups;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.invariants.lib.crdts.GSet;

import java.io.Serializable;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;

/**
 * Created on 04.04.19.
 *
 * @author Mirko Köhler
 */
@ReplicatedModel
public class Inbox implements Serializable, Mergeable<Inbox> {
    public final GSet<String> entries = new GSet();

    static { /* Prevent IntelliJ from removing the import */ stateful(null); }

    //@ ensures entries.isEmpty();
    public Inbox() {}

    //@ assignable entries;
    public Void add(String msg) {
        /* Weak */
        entries.add(msg);
        return null;
    }

    //@ ensures stateful(entries.merge(other.entries));
    @Override
    public Void merge(Inbox other) {
        entries.merge(other.entries);
        return null;
    }
}
