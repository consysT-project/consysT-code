package de.tuda.stg.consys.core.store

sealed trait CoordinationMechanism

object CoordinationMechanism {
	case class Zookeeper(port: Int) extends CoordinationMechanism
	case class ETCD(port: Int) extends CoordinationMechanism
}
