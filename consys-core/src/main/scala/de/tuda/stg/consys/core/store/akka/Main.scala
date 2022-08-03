package de.tuda.stg.consys.core.store.akka

import akka.actor.ExtendedActorSystem
import akka.actor.typed.ActorSystem
import akka.cluster.ddata.LWWRegister
import akka.cluster.ddata.typed.scaladsl.DistributedData
import com.typesafe.config.{ConfigFactory, ConfigValueFactory}
import de.tuda.stg.consys.Mergeable
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica.Loop
import de.tuda.stg.consys.core.store.akka.levels.Weak
import org.checkerframework.dataflow.qual.SideEffectFree

import scala.collection.mutable

object Main {

  case class Box(var f : Any) extends java.io.Serializable {
    @SideEffectFree def get : Any = f
  }

  class MergeableSet(elems : Iterable[Int]) extends Mergeable[MergeableSet] with java.io.Serializable {

    val underlying : mutable.Set[Int] = mutable.HashSet.empty
    underlying.addAll(elems)

    override def merge(other : MergeableSet) : Void = {
      underlying.addAll(other.underlying)
      null
    }

    override def toString : String = s"Mergeable<$underlying>"
  }


  def main(args : Array[String]) {

    val store1 = AkkaStore.fromAddress("127.0.0.1", 4445)
    val store2 = AkkaStore.fromAddress("127.0.0.2", 4446)

    store1.replica.addOtherReplica(store2.getAddress)
    store2.replica.addOtherReplica(store1.getAddress)



    store1.transaction(ctx => {
      val set1 = ctx.replicate[MergeableSet]("set1", Weak, List(23,42))
      println("Done 1")
      Some(())
    })

    Thread.sleep(1000)

    store2.transaction(ctx => {
      val set1 = ctx.replicate[MergeableSet]("set1", Weak, List(24,43))
      println("Done 2")
      Some(())
    })

    Thread.sleep(1000)

    store1.transaction(ctx => {
      val set1 = ctx.lookup[MergeableSet]("set1", Weak)
      val result = set1.resolve(ctx).invoke[String]("toString", Seq())
      println(result)
      Some(())
    })
  }
}