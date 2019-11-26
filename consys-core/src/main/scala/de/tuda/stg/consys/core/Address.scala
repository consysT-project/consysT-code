package de.tuda.stg.consys.core

/**
 * Created on 25.11.19.
 *
 * @author Mirko Köhler
 */
case class Address(hostname : String, port : Int) {
	override def toString : String = s"$hostname:$port"
}

object Address {
	def parse(addressString : String) : Address = {
		val splitted = addressString.split(":", 2)
		Address(splitted(0), splitted(1).toInt)
	}
}
