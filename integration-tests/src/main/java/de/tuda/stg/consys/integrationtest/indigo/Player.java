package de.tuda.stg.consys.integrationtest.indigo;

import de.tuda.stg.consys.checker.qual.Mutable;

public class Player {
	
	private final String name;
	private int budget = 0;

	public Player(@Mutable String name) {
		this.name = name;
	}
	
	public int getBudget() {
		return budget;
	}
	
	public void incBudget(int amount) {
		budget += amount;
	}
}
