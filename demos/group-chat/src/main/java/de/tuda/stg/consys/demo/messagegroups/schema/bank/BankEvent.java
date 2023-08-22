package de.tuda.stg.consys.demo.messagegroups.schema.bank;

import java.io.Serializable;

public interface BankEvent {

	boolean isWithdraw();
	boolean isDeposit();

	int getAmount();


	class Withdraw implements BankEvent, Serializable {
		public final int amount;

		public Withdraw(int amount) {
			this.amount = amount;
		}

		@Override
		public boolean isWithdraw() {
			return true;
		}

		@Override
		public boolean isDeposit() {
			return false;
		}

		@Override
		public int getAmount() {
			return amount;
		}
	}

	class Deposit implements BankEvent, Serializable {
		public final int amount;

		public Deposit(int amount) {
			this.amount = amount;
		}

		@Override
		public boolean isWithdraw() {
			return false;
		}

		@Override
		public boolean isDeposit() {
			return true;
		}

		@Override
		public int getAmount() {
			return amount;
		}
	}

}
