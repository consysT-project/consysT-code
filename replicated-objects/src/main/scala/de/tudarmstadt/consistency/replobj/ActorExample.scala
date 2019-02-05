package de.tudarmstadt.consistency.replobj

/**
	* Created on 05.02.19.
	*
	* @author Mirko Köhler
	*/
object ActorExample extends App {


	import akka.actor.{ ActorSystem, Actor, ActorRef, Props, PoisonPill }
	import language.postfixOps
	import scala.concurrent.duration._

	case object Ping
	case object Pong

	class Pinger extends Actor {
		var countDown = 100

		def receive = {
			case Pong ⇒
				println(s"${self.path} received pong, count down $countDown")

				if (countDown > 0) {
					countDown -= 1
					sender() ! Ping
				} else {
					sender() ! PoisonPill
					self ! PoisonPill
				}
		}
	}

	class Ponger(pinger: ActorRef) extends Actor {
		def receive = {
			case Ping ⇒
				println(s"${self.path} received ping")
				pinger ! Pong
		}
	}


	val system = ActorSystem("pingpong")

	val pinger = system.actorOf(Props[Pinger], "pinger")

	val ponger = system.actorOf(Props(classOf[Ponger], pinger), "ponger")

	import system.dispatcher
	system.scheduler.scheduleOnce(500 millis) {
		ponger ! Ping
	}
}
