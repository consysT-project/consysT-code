package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.TransactionContext
import de.tuda.stg.consys.core.store.akka.backend.AkkaObject
import de.tuda.stg.consys.core.store.akka.backend.AkkaReplicaAdapter.{CreateOrUpdateObject, TransactionOp}
import de.tuda.stg.consys.core.store.akka.levels.Strong
import de.tuda.stg.consys.core.store.extensions.ReflectiveObject
import de.tuda.stg.consys.core.store.extensions.coordination.{DistributedLock, LockingTransactionContext, ZookeeperLockingTransactionContext}
import de.tuda.stg.consys.core.store.extensions.transaction.{CachedTransactionContext, CommitableTransactionContext}
import de.tuda.stg.consys.core.store.utils.Reflect

import scala.collection.mutable
import scala.reflect.ClassTag

class AkkaTransactionContext(override val store: AkkaStore) extends CachedTransactionContext[AkkaStore]
  with CommitableTransactionContext[AkkaStore]
  with ZookeeperLockingTransactionContext[AkkaStore] {

  override type CachedType[T <: AkkaStore#ObjType] = AkkaCachedObject[T]



  override def replicate[T <: AkkaStore#ObjType : ClassTag](addr: AkkaStore#Addr, level: AkkaStore#Level, constructorArgs: Any*): AkkaStore#RefType[T] = {
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

  override def lookup[T <: AkkaStore#ObjType : ClassTag](addr: AkkaStore#Addr, level: AkkaStore#Level): AkkaStore#RefType[T] = {
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

    //TODO: Add synchronized write for Strong objects
    if (containsStrong)
      store.replica.writeSync(timestamp, ops.toSeq)
    else
      store.replica.writeAsync(timestamp, ops.toSeq)
  }
}



