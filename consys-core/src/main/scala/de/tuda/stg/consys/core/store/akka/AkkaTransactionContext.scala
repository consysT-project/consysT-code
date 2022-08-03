package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.TransactionContext
import de.tuda.stg.consys.core.store.akka.backend.AkkaObject
import de.tuda.stg.consys.core.store.akka.backend.BackendReplica.{CreateOrUpdateObject, TransactionOp}
import de.tuda.stg.consys.core.store.extensions.ReflectiveObject
import de.tuda.stg.consys.core.store.extensions.transaction.{CachedTransactionContext, CommitableTransactionContext}
import de.tuda.stg.consys.core.store.utils.Reflect

import scala.collection.mutable
import scala.reflect.ClassTag

class AkkaTransactionContext(override val store: AkkaStore) extends CachedTransactionContext[AkkaStore]
  with CommitableTransactionContext[AkkaStore] {

  override type CachedType[T <: AkkaStore#ObjType] = CachedObject[T]

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

    Cache.buffer.values.foreach(cacheElement => {
      if (cacheElement.changedObject) {
        ops.append(CreateOrUpdateObject(cacheElement.data.addr, cacheElement.data.state, cacheElement.data.level))
      }
    })

    val timestamp = System.currentTimeMillis()
    store.replica.write(timestamp, ops.toSeq)
  }
}

case class CachedObject[T <: AkkaStore#ObjType : ClassTag](override val addr : AkkaStore#Addr, override val state : T, level : AkkaStore#Level)
  extends ReflectiveObject[AkkaStore#Addr, T]

