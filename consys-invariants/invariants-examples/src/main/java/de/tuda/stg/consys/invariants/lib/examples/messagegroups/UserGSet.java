package de.tuda.stg.consys.invariants.lib.examples.messagegroups;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

/* Specialized class for GSet<User>. Ugly but necessary as GSet<User> is not handled correctly by the solver. */
@ReplicatedModel
public class UserGSet implements Mergeable<UserGSet>, Serializable {
    public Set<User> underlying;

    /* Constructors */
    //@ ensures underlying.isEmpty();
    public UserGSet() {
        this.underlying = new HashSet<User>();
    }

    //@ assignable underlying;
    //@ ensures underlying.contains(val);
    //@ ensures underlying.containsAll(\old(underlying));
    @WeakOp public Void add(User val) {
        underlying.add(val);
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.contains(val);
    @SideEffectFree @WeakOp public boolean contains(User val){
        return underlying.contains(val);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.isEmpty();
    @SideEffectFree @WeakOp public boolean isEmpty() {
        return underlying.isEmpty();
    }

    //@ assignable \nothing;
    //@ ensures \result.equals(underlying);
    @SideEffectFree @WeakOp public Set<User> getValue() {
        return underlying;
    }

    //@ ensures (\forall User i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    //@ ensures (\forall User i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    public Void merge(UserGSet other) {
        underlying.addAll(other.underlying);
        return null;
    }
}