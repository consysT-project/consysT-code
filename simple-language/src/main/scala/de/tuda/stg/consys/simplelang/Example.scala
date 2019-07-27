package de.tuda.stg.consys.simplelang

import java.util.Date

import scala.collection.mutable

/**
	* Created on 29.05.19.
	*
	* @author Mirko Köhler
	*/

/*
	Defined by the system.
 */
trait Shared[T] {
	def ref : T
}

object Defs {
	def shared[T](obj : T) : Shared[T] = new Shared[T] {
		override def ref : T = obj
	}

	def transaction[T](f : => T) : T = f
}



/*
	Defined by the user.
 */
trait Server {
	import Defs._
	val concerts : Shared[mutable.Map[Int, Concert]] = shared(mutable.HashMap.empty)
}

object Server1 extends App with Server {
	import Defs._

	val loc1 : Shared[Location] = shared(new Location("Schlachthof", 500))
	val loc2 : Shared[Location] = shared(new Location("Villa", 500))
	val band1 : Shared[Band] = shared(new Band("Ivan"))

	concerts.ref.put(0, new Concert("2019-05-06", band1, loc1))
	concerts.ref.put(1, new Concert("2019-05-08", band1, loc2))

}

trait Client {
	import Defs._
	val concerts : Shared[mutable.Map[Int, Concert]] = shared(null)
}

object Client1 extends App with Client {
	import Defs._

	concerts.ref.get(1) match {

		case None => println("concert not available")

		case Some(concert) => transaction {
			(concert.buyTicket(), concert.buyTicket()) match {
				case (None, None) => println("no ticket available")
				case _ => println("Some tickets where bought")
			}
		}

	}
}





class Band(val name : String)

class Location(val name : String, val seats : Int)

class Ticket(val concert : Concert)

class Concert(val date : String, val band : Shared[Band], val location : Shared[Location]) {

	var soldTickets : Int = 0

	def buyTicket() : Option[Ticket] = {
		if (soldTickets < location.ref.seats) {
			soldTickets += 1
			Some(new Ticket(this))
		} else {
			None
		}
	}
}