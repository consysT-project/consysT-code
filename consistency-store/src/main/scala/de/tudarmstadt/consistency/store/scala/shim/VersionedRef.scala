package de.tudarmstadt.consistency.store.scala.shim

import de.tudarmstadt.consistency.store.scala.impl.ReadWriteRef

trait VersionedRef[Key, T] extends ReadWriteRef[Key, T]