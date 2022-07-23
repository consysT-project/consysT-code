package de.tuda.stg.consys.core.store.akka

import akka.actor.ExtendedActorSystem
import akka.actor.typed.ActorSystem
import akka.cluster.ddata.LWWRegister
import akka.cluster.ddata.typed.scaladsl.DistributedData
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.core.store.akka.levels.Weak

object Main {

  case class Box(var f : Any) extends java.io.Serializable {
    def get : Any = f
  }


  def main(args : Array[String]) {

    val config = ConfigFactory.load()
      .withValue("akka.remote.artery.canonical.hostname", ConfigValueFactory.fromAnyRef("127.0.0.1"))
      .withValue("akka.remote.artery.canonical.port", ConfigValueFactory.fromAnyRef(4445))
      .resolve()

    //Creates the actor system
    val system = akka.actor.ActorSystem("MY_ACTOR_SYSTEM", config)
    system.log.info(s"created replica actor system at ${system.asInstanceOf[ExtendedActorSystem].provider.getDefaultAddress}")

    val store = new AkkaStore(system)

    store.transaction(ctx => {
      val box1 = ctx.replicate[Box]("box1", Weak, 42)
      Some(())
    })

    val result = store.transaction(ctx => {
      val box1 = ctx.lookup[Box]("box1", Weak)
      val value = box1.resolve(ctx).invoke("get", Seq())
      Some(value)
    })

    println(result)




  }
}