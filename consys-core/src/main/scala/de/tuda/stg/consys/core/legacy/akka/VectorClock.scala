package de.tuda.stg.consys.core.legacy.akka

import scala.collection.immutable.TreeMap

final case class VectorClock (vcName: String, versions: TreeMap[String, Int] = TreeMap.empty[String, Int]) {

  def inc : VectorClock = {
    val currentTimestamp : Int = versions.getOrElse(vcName, 0)
    copy(versions = versions.updated(vcName, currentTimestamp + 1))
  }

  def merge (that: VectorClock): VectorClock = {
    var mergedVersions = that.versions
    for ((key, time) <- versions) {
      val mergedVersionsCurrentTime: Int = mergedVersions.getOrElse(key, 0)
      if (time > mergedVersionsCurrentTime)
        mergedVersions = mergedVersions.updated(key, time)
    }
    VectorClock(vcName, mergedVersions)
  }

  def happenedBefore (that: VectorClock): Boolean = {
    val checkVersions = that.versions
    var check : Boolean = true
    for ((key, time) <- versions) {
      val CheckVersionsCurrentTime : Int = checkVersions.getOrElse(key, 0)
      if (key == vcName) {
        check &= (time == CheckVersionsCurrentTime + 1)
      } else {
        check &= (time <= CheckVersionsCurrentTime)
      }
    }
    check
  }


  override def toString = vcName + ": " + versions.map { case (_, t) => s"$t" }.mkString("(", ", ", ")")
}