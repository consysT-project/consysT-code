package de.tuda.stg.consys.demo.invariantdemos.schema.tournament;

import de.tuda.stg.consys.annotations.invariants.DataModel;

import java.io.Serializable;

@DataModel public class Player implements Serializable {

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
