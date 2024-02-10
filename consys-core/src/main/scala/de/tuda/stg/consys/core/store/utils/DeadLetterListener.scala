package de.tuda.stg.consys.core.store.utils

import akka.actor.{Actor, ActorSystem, AllDeadLetters, Props}
import de.tuda.stg.consys.logging.Logger

class DeadLetterListener extends Actor {

  def receive = {
    case m => Logger.info(m)
  }

}

object DeadLetterListener {

  def addDeadLetterListener(system : ActorSystem) : Unit = {
    val deadLetterListener = system.actorOf(Props[DeadLetterListener]())
    system.eventStream.subscribe(deadLetterListener, classOf[AllDeadLetters])
  }
}