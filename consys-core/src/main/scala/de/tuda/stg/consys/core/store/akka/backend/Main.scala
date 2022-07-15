package de.tuda.stg.consys.core.store.akka.backend

import akka.actor.ExtendedActorSystem
import akka.actor.typed.ActorSystem
import akka.cluster.ddata.LWWRegister
import akka.cluster.ddata.typed.scaladsl.DistributedData
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica.{CreateObject, UpdateObject}

object Main {

  case class Record(version : Int, name : String, address : String)

  def distributedDataExample() : Unit = {
    //Loads the reference.conf for the akka properties
    val config = ConfigFactory.load()
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef("127.0.0.1"))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(4445))
      .resolve()

    //Creates the actor system
    val internalSystem = akka.actor.ActorSystem("MY_ACTOR_SYSTEM", config)
    internalSystem.log.info(s"created replica actor system at ${internalSystem.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

    val system = ActorSystem.wrap(internalSystem)

    val node = DistributedData(system).selfUniqueAddress
    val recordClock = new LWWRegister.Clock[Record] {
      override def apply(currentTimestamp : Long, value : Record) : Long =
        value.version
    }

    val record1 = Record(version = 1, "Alice", "Union Square")
    var reg = LWWRegister.create(node, record1, recordClock)

    val record2 = Record(version = 2, "Alice", "Madison Square")
    reg = reg.withValue(node, record2)

    println(reg.getValue())
  }

  def replicaExample() : Unit = {

  }


  def main(args : Array[String]) {

    val config = ConfigFactory.load()
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef("127.0.0.1"))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(4445))
      .resolve()

    //Creates the actor system
    val internalSystem = akka.actor.ActorSystem("MY_ACTOR_SYSTEM", config)
    internalSystem.log.info(s"created replica actor system at ${internalSystem.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

    val system = ActorSystem.wrap(internalSystem)

    val replica = new BackendReplica(internalSystem)

    replica.write(Seq(CreateObject("001", 42, "Weak"), UpdateObject("001", 31, "Weak")))
    val result = replica.read[Int]("001")

    println(result)




  }
}