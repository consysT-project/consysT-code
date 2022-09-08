package de.tuda.stg.consys.invariants.lib.crdts.immutable;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.__merge;


@ReplicatedModel public class PNCounter implements Mergeable<PNCounter> {

    public GCounter incCounter = new GCounter();
    public GCounter decCounter = new GCounter();

    /* Constructors */
    //@ ensures incCounter.getValue() == 0 && decCounter.getValue() == 0;
    public PNCounter() {

    }


    //@ assignable \nothing;
    //@ ensures \result == incCounter.getValue() - decCounter.getValue();
    public int getValue() { return incCounter.getValue() - decCounter.getValue(); }




    //@ assignable incCounter;
    //@ ensures stateful( incCounter.inc() );
    public Void inc() {
        incCounter.inc();
        return null;
    }

    //@ requires n >= 0;
    //@ assignable incCounter;
    //@ ensures stateful( incCounter.inc(n) );
    public Void inc(int n) {
        if (n < 0) throw new IllegalArgumentException();
        incCounter.inc(n);
        return null;
    }


    //@ assignable decCounter;
    //@ ensures stateful( decCounter.inc() );
    public Void dec() {
        decCounter.inc();
        return null;
    }


    //@ requires n >= 0;
    //@ assignable decCounter;
    //@ ensures stateful( decCounter.inc(n) );
    public Void dec(int n) {
        if (n < 0) throw new IllegalArgumentException();
        decCounter.inc(n);
        return null;
    }

    //@ assignable incCounter, decCounter;
    //@ ensures stateful( incCounter.merge(other.incCounter) );
    //@ ensures stateful( decCounter.merge(other.decCounter) );
    public Void merge(PNCounter other) {
        incCounter.merge(other.incCounter);
        decCounter.merge(other.decCounter);

        return null;
    }
}
