package de.tuda.stg.consys.invariants.lib.examples.tournament;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class GSetPlayer implements Mergeable<GSetPlayer>, Serializable {

    public Set<Player> underlying;

    /* Constructors */
    //@ ensures underlying.isEmpty();
    public GSetPlayer() {
        this.underlying = new HashSet();
    }

    //@ assignable underlying;
    //@ ensures underlying.contains(val);
    //@ ensures underlying.containsAll(\old(underlying));
    @WeakOp public void add(Player val) {
        underlying.add(val);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.contains(val);
    @SideEffectFree
    @WeakOp public boolean contains(Player val){
        return underlying.contains(val);
    }

    //@ assignable \nothing;
    //@ underlying.isEmpty();
    @SideEffectFree @WeakOp public boolean isEmpty() {
        return underlying.isEmpty();
    }

    //@ ensures (\forall Player i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    //@ ensures (\forall Player i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    public Void merge(GSetPlayer other) {
        underlying.addAll(other.underlying);
        return null;
    }
}