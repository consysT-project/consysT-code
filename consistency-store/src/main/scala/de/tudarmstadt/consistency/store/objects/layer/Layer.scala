package de.tudarmstadt.consistency.store.objects.layer

import de.tudarmstadt.consistency.store.objects.store.Store
import de.tudarmstadt.consistency.store.objects.{Bindings, DistributedObjectLanguage}

/**
	* Created on 26.11.18.
	*
	* @author Mirko Köhler
	*/
trait Layer {
	self : DistributedObjectLanguage =>

	case class StoreRef[T](addr : B#Address, consistency : B#Consistency)

	val store : Store
	import store._

	type B = store.B

	val k : ProcessId

	def enref[T](value : T, consistency : B#Consistency) : StoreRef[T]
	def deref[T](ref : StoreRef[T]) : T
	def update[T](ref : StoreRef[T], value : T) : Unit

}
