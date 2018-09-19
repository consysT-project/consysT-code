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

	def transfer(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(from : Key, to : Key, amount : Integer) : Unit = {
		val readFrom = tx.read(from, consistencyLevel)

		val readTo = tx.read(to, consistencyLevel)

		(readFrom, readTo) match {
			case (Some(a), Some(b)) =>
				tx.write(from, a - amount, consistencyLevel)
				tx.write(to, b + amount, consistencyLevel)
			case r =>
				println(s"r = $r")
				tx.abort()
		}
	}

	def withdraw(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(account : Key, amount : Integer) : Unit = {
		tx.read(account, consistencyLevel) match {
			case Some(a) =>
				tx.write(account, a - amount, consistencyLevel)
			case r =>
				tx.abort()
		}
	}

	def deposit(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(account : Key, amount : Integer) : Unit = {
		tx.read(account, consistencyLevel) match {
			case Some(a) =>
				tx.write(account, a + amount, consistencyLevel)
			case r =>
				//Depositing on an empty account
				tx.write(account, amount, consistencyLevel)
		}
	}

	def getBalance(tx : ITxContext[Key, Integer, Consistency, Consistency, Option[Integer]], consistencyLevel : Consistency)(account : Key) : Integer = {
		tx.read(account, consistencyLevel) match {
			case Some(a) =>
				a
			case r =>
				assert(false, s"the balance have not been read, instead: $r")
				???
		}
	}




}
