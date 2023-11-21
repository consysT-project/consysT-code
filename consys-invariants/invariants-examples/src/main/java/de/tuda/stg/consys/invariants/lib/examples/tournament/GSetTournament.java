package de.tuda.stg.consys.invariants.lib.examples.tournament;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class GSetTournament implements Mergeable<GSetTournament>, Serializable {

    public Set<Tournament> underlying;

    /* Constructors */
    //@ ensures underlying.isEmpty();
    public GSetTournament() {
        this.underlying = new HashSet();
    }

    //@ assignable underlying;
    //@ ensures underlying.contains(val);
    //@ ensures underlying.containsAll(\old(underlying));
    @WeakOp public void add(Tournament val) {
        underlying.add(val);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.contains(val);
    @SideEffectFree @WeakOp public boolean contains(Tournament val){
        return underlying.contains(val);
    }

    //@ assignable \nothing;
    //@ underlying.isEmpty();
    @SideEffectFree @WeakOp public boolean isEmpty() {
        return underlying.isEmpty();
    }

    //@ ensures (\forall Tournament i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    //@ ensures (\forall Tournament i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    public Void merge(GSetTournament other) {
        underlying.addAll(other.underlying);
        return null;
    }
}