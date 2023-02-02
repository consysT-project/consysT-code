package org.conloc.invariants.lib.examples.tournament;

import org.conloc.annotations.invariants.ReplicatedModel;

import java.util.HashSet;
import java.util.Set;

import static org.conloc.invariants.utils.InvariantUtils.numOfReplicas;
import static org.conloc.invariants.utils.InvariantUtils.replicaId;
import static org.conloc.invariants.utils.InvariantUtils.stateful;

@ReplicatedModel public class GSetTournament {

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