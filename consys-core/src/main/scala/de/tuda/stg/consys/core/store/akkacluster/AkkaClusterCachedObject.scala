package de.tuda.stg.consys.core.store.akkacluster

import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterCachedObject.ReadLevel
import de.tuda.stg.consys.core.store.extensions.ReflectiveObject

import scala.reflect.ClassTag

private[akkacluster] case class AkkaClusterCachedObject[T <: AkkaClusterStore#ObjType : ClassTag](
	override val addr : AkkaClusterStore#Addr,
	override val state : T,
	level : AkkaClusterStore#Level,
	readLevel : ReadLevel
) extends ReflectiveObject[AkkaClusterStore#Addr, T]


object AkkaClusterCachedObject {

	sealed trait ReadLevel
	case object ReadWeak extends ReadLevel
	case object ReadStrong extends ReadLevel

}

