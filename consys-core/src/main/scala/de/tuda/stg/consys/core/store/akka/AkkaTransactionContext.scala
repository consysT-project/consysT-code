package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.TransactionContext
import de.tuda.stg.consys.core.store.akka.backend.AkkaObject
import de.tuda.stg.consys.core.store.akka.backend.AkkaReplicaAdapter.{CreateOrUpdateObject, TransactionOp}
import de.tuda.stg.consys.core.store.akka.levels.Strong
import de.tuda.stg.consys.core.store.extensions.ReflectiveObject
import de.tuda.stg.consys.core.store.extensions.coordination.LockingTransactionContext
import de.tuda.stg.consys.core.store.extensions.transaction.{CachedTransactionContext, CommitableTransactionContext}
import de.tuda.stg.consys.core.store.utils.Reflect

import java.lang.reflect.Field
import scala.collection.mutable
import scala.reflect.ClassTag

abstract class AkkaTransactionContext[StoreType <: AkkaStore](override val store: StoreType) extends CachedTransactionContext[StoreType, Field]
  with CommitableTransactionContext[StoreType]
  with LockingTransactionContext[StoreType] {

  override type CachedType[T <: StoreType#ObjType] = AkkaCachedObject[T]



  override def replicate[T <: StoreType#ObjType : ClassTag](addr: StoreType#Addr, level: StoreType#Level, constructorArgs: Any*): StoreType#RefType[T] = {
    def callConstructor[C](clazz : ClassTag[C], args : Any*) : C = {
      val constructor = Reflect.getConstructor(clazz.runtimeClass, args : _*)
      constructor.newInstance(args.map(e => e.asInstanceOf[AnyRef]) : _*).asInstanceOf[C]
    }

    // Creates a new object by calling the matching constructor
    val obj = callConstructor[T](implicitly[ClassTag[T]], constructorArgs : _*)

    // Get the matching protocol and execute replicate
    val protocol = level.toProtocol(store)
    val ref = protocol.replicate[T](this, addr, obj)
    ref
  }

  override def lookup[T <: StoreType#ObjType : ClassTag](addr: StoreType#Addr, level: StoreType#Level): StoreType#RefType[T] = {
    val protocol = level.toProtocol(store)
    val ref = protocol.lookup[T](this, addr)
    ref
  }

  override private[store] def commit() : Unit = {
    val ops = mutable.Buffer.empty[TransactionOp]

    var containsStrong = false
    Cache.buffer.values.foreach(cacheElement => {
      if (cacheElement.changedObject) {
        containsStrong = containsStrong || cacheElement.data.level == Strong
        ops.append(CreateOrUpdateObject(cacheElement.data.addr, cacheElement.data.state))
      }
    })

    val timestamp = System.currentTimeMillis()

    //TODO: Add synchronized write for Strong objects only?
    if (containsStrong)
      store.replica.writeSync(timestamp, ops.toSeq)
    else
      store.replica.writeAsync(timestamp, ops.toSeq)
  }
}



