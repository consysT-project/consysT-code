package de.tuda.stg.consys.core.store.akka.backend

import de.tuda.stg.consys.core.store.akka.backend.BackendReplica.{Addr, Level, ObjType}
import de.tuda.stg.consys.core.store.extensions.ReflectiveObject

import scala.reflect.ClassTag

case class AkkaObject[T <: ObjType : ClassTag](
    override val addr : Addr, override val state : T, val level : Level
) extends ReflectiveObject[Addr, T] with Serializable

