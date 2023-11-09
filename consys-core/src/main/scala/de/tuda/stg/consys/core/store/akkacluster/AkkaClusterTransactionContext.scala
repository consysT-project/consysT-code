package de.tuda.stg.consys.core.store.akkacluster

import de.tuda.stg.consys.core.store.akka.levels.Strong
import de.tuda.stg.consys.core.store.akkacluster.backend.AkkaClusterReplicaAdapter.{CreateOrUpdateObject, TransactionOp}
import de.tuda.stg.consys.core.store.extensions.coordination.ZookeeperLockingTransactionContext
import de.tuda.stg.consys.core.store.extensions.transaction.{CachedTransactionContext, CommitableTransactionContext}
import de.tuda.stg.consys.core.store.utils.Reflect

import scala.collection.mutable
import scala.reflect.ClassTag

class AkkaClusterTransactionContext(override val store: AkkaClusterStore) extends CachedTransactionContext[AkkaClusterStore]
  with CommitableTransactionContext[AkkaClusterStore]
  with ZookeeperLockingTransactionContext[AkkaClusterStore] {

  override type CachedType[T <: AkkaClusterStore#ObjType] = AkkaClusterCachedObject[T]



  override def replicate[T <: AkkaClusterStore#ObjType : ClassTag](addr: AkkaClusterStore#Addr, level: AkkaClusterStore#Level, constructorArgs: Any*): AkkaClusterStore#RefType[T] = {
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

  override def lookup[T <: AkkaClusterStore#ObjType : ClassTag](addr: AkkaClusterStore#Addr, level: AkkaClusterStore#Level): AkkaClusterStore#RefType[T] = {
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
      store.replica.writeAll(timestamp, ops.toSeq)
    else
      store.replica.writeLocal(timestamp, ops.toSeq)
  }
}



