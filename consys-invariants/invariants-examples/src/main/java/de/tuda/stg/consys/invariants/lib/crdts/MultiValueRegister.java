package de.tuda.stg.consys.invariants.lib.crdts;

import com.google.common.collect.ImmutableSet;
import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class MultiValueRegister implements Mergeable<MultiValueRegister>, Serializable {

    public final Set<Object> value;

    //@ public invariant (\exists Object o; true; value.contains(o) );

    //@ ensures value.contains(initial);
    public MultiValueRegister(Object initial) {
        value = new HashSet<>();
        value.add(initial);
    }

    //@ ensures (\forall Object o; true; o == val ? value.contains(o) : !value.contains(o) );
    @WeakOp public Void write(Object val) {
        value.clear();
        value.add(val);
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == value;
    @SideEffectFree @WeakOp public Set<Object> read() {
        return ImmutableSet.copyOf(value);
    }

    //@ ensures (\forall Object o; true; \old(value).contains(o) || other.value.contains(o) ?  value.contains(o) : !value.contains(o));
    public Void merge(MultiValueRegister other) {
        value.addAll(other.value);
        return null;
    }
}
