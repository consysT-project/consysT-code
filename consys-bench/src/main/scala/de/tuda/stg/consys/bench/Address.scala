package de.tuda.stg.consys.bench

/**
 * Created on 29.10.19.
 *
 * @author Mirko Köhler
 */
case class Address(hostname : String, port : Int) {
	override def toString : String = s"$hostname:$port"
}

object Address {
	def create(addressString : String) : Address = {
		val splitted = addressString.split(":", 2)
		Address(splitted(0), splitted(1).toInt)
	}
}
