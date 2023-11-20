package de.tuda.stg.consys.invariants.lib.examples.tournament;

import de.tuda.stg.consys.annotations.invariants.DataModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

@DataModel public class Player {

    private final String name;
    private int budget = 0;

    public Player(String name) {
        this.name = name;
    }

    //@ assignable \nothing;
    @SideEffectFree @WeakOp
    public int getBudget() {
        return budget;
    }

    //@ assignable budget;
    @WeakOp public void incBudget(int amount) {
        budget += amount;
    }
}
