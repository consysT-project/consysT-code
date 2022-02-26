package de.tuda.stg.consys.core.store.utils

/**
 * Created on 25.11.19.
 *
 * @author Mirko Köhler
 */
case class Address(hostname : String, port : Int) {
	override def toString : String = s"$hostname:$port"
}

case class MultiPortAddress(hostname : String, port1 : Int, port2 : Int) {
	override def toString : String = s"$hostname:$port1:$port2"
}

object Address {
	def parse(addressString : String) : Address = {
		val splitted = addressString.split(":", 2)
		Address(splitted(0), splitted(1).toInt)
	}
}

object MultiPortAddress {
	def parse(addressString : String) : MultiPortAddress = {
		val splitted = addressString.split(":", 3)
		MultiPortAddress(splitted(0), splitted(1).toInt, splitted(2).toInt)
	}
}
