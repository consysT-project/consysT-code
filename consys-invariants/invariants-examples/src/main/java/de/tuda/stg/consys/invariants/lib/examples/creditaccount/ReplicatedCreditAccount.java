package de.tuda.stg.consys.invariants.lib.examples.creditaccount;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.invariants.lib.crdts.PNCounter;
import org.checkerframework.dataflow.qual.SideEffectFree;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.stateful;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;




@ReplicatedModel
public class ReplicatedCreditAccount implements Mergeable<ReplicatedCreditAccount> {

    public final PNCounter credits;

    /* Invariants */
    //@ public invariant getValue() >= 0;

    //@ ensures getValue() == 0;
    //@ ensures credits.getValue() == 0;
    public ReplicatedCreditAccount() {
        credits = new PNCounter(replicaId());
    }

    /* Methods */
    //@ assignable \nothing;
    //@ ensures \result == \old(credits.getValue());
    @SideEffectFree
    @WeakOp public int getValue() {
        return credits.getValue();
    }


    //@ requires val >= 0;
    //@ assignable credits;
    //@ ensures stateful( credits.inc(val) );
    @WeakOp public void deposit(int val) {
        if (0 > val) throw new IllegalArgumentException();
        credits.inc(val);
    }


    //@ requires 0 <= val && val <= getValue();
    //@ assignable credits;
    //@ ensures stateful( credits.dec(val) );
    @StrongOp public void withdraw(int val) {
        if (0 > val || val > getValue()) throw new IllegalArgumentException();
        credits.dec(val);
    }

    //TODO: Why does the merge method not check all of a sudden?!?
    /* Merge method */
    //@ requires (\sum int i; i >= 0 && i < numOfReplicas(); Math.max(credits.incs[i], other.credits.incs[i]) - Math.max(credits.decs[i], other.credits.decs[i])) >= 0;
    //@ ensures stateful( credits.merge(other.credits) );
    public Void merge(ReplicatedCreditAccount other) {
        credits.merge(other.credits);
        return null;
    }
}