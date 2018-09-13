package de.tudarmstadt.consistency.store.examples

import de.tudarmstadt.consistency.store.Store.ITxContext

/**
	* Created on 13.09.18.
	*
	* @author Mirko Köhler
	*/
trait BankingStore {

	type Key
	type Consistency

	def transfer(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(from : Key, to : Key, amount : Int) : Unit = {
		(tx.read(from, consistencyLevel), tx.read(to, consistencyLevel)) match {
			case (Some(a), Some(b)) =>
				tx.update(from, a - amount, consistencyLevel)
				tx.update(to, b + amount, consistencyLevel)
			case r =>
				assert(false, s"transfer was not executed as the account balances have not been read, got: $r")
		}
	}

	def withdraw(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(account : Key, amount : Int) : Unit = {
		tx.read(account, consistencyLevel) match {
			case Some(a) =>
				tx.update(account, a - amount, consistencyLevel)
			case r =>
				assert(false, s"withdraw was not executed as the account balance have not been read, got: $r")
		}
	}

	def deposit(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(account : Key, amount : Int) : Unit = {
		tx.read(account, consistencyLevel) match {
			case Some(a) =>
				tx.update(account, a + amount, consistencyLevel)
			case r =>
				//Depositing on an empty account
				tx.update(account, amount, consistencyLevel)
		}
	}

	def getBalance(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(account : Key) : Int = {
		tx.read(account, consistencyLevel) match {
			case Some(a) =>
				a
			case r =>
				assert(false, s"the balance have not been read, instead: $r")
				???
		}
	}




}
