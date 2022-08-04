package de.tuda.stg.consys.core.store.akka

import de.tuda.stg.consys.core.store.extensions.ReflectiveObject

import scala.reflect.ClassTag

private[akka] case class AkkaCachedObject[T <: AkkaStore#ObjType : ClassTag](override val addr : AkkaStore#Addr, override val state : T, level : AkkaStore#Level)
    extends ReflectiveObject[AkkaStore#Addr, T]