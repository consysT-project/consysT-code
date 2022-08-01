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

    val store1 = AkkaStore.fromAddress("127.0.0.1", 4445)
    val store2 = AkkaStore.fromAddress("127.0.0.2", 4446)

    store1.replica.addOtherReplica(store2.getAddress)
    store2.replica.addOtherReplica(store1.getAddress)

    store1.transaction(ctx => {
      val box1 = ctx.replicate[Box]("box1", Weak, 42)
      println("Done 1")
      Some(())
    })

    val result = store2.transaction(ctx => {
      val box1 = ctx.lookup[Box]("box1", Weak)
      val value = box1.resolve(ctx).invoke("get", Seq())
      println("Done 2")
      Some(value)
    })

    println(result)




  }
}