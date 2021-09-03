package de.tuda.stg.consys.demo.invariantdemos.schema.tournament;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class GSetTournament implements Serializable {

    public Set<Tournament> underlying;

    /* Constructors */
    //@ ensures underlying.isEmpty();
    public GSetTournament() {
        this.underlying = new HashSet();
    }

    /*@
    @ assignable underlying;
    @ ensures underlying.contains(val);
    @ ensures underlying.containsAll(\old(underlying));
    @*/
    public void add(Tournament val) {
        underlying.add(val);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.contains(val);
    public boolean contains(Tournament val){
        return underlying.contains(val);
    }

    //@ underlying.isEmpty();
    public boolean isEmpty() {
        return underlying.isEmpty();
    }

    //@ ensures (\forall Tournament i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    //@ ensures (\forall Tournament i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    public void merge(GSetTournament other) {
        underlying.addAll(other.underlying);
    }
}