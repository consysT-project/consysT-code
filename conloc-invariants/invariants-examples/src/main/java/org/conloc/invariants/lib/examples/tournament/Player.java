package org.conloc.invariants.lib.examples.tournament;

import org.conloc.annotations.invariants.DataModel;

import static org.conloc.invariants.utils.InvariantUtils.numOfReplicas;
import static org.conloc.invariants.utils.InvariantUtils.replicaId;
import static org.conloc.invariants.utils.InvariantUtils.stateful;

@DataModel public class Player {

    private final String name;
    private int budget = 0;

    public Player(String name) {
        this.name = name;
    }

    //@ assignable \nothing;
    public int getBudget() {
        return budget;
    }

    //@ assignable budget;
    public void incBudget(int amount) {
        budget += amount;
    }
}
