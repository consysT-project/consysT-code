package de.tuda.stg.consys.integrationtest.indigo;

public class Player {
	
	private final String name;
	private int budget = 0;

	public Player(String name) {
		this.name = name;
	}
	
	public int getBudget() {
		return budget;
	}
	
	public void incBudget(int amount) {
		budget += amount;
	}
}
