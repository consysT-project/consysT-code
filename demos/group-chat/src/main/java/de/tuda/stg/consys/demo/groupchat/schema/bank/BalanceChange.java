package de.tuda.stg.consys.demo.groupchat.schema.bank;

import java.io.Serializable;

public class BalanceChange implements Serializable {
	private final int amount;

	public BalanceChange(int amount) {
		this.amount = amount;
	}

	public int getAmount() {
		return amount;
	}
}
