package de.tudarmstadt.consistency.store.objects

/**
	* Created on 26.11.18.
	*
	* @author Mirko Köhler
	*/
trait Bindings {

	type Address

	type Consistency
	type ConsistencyLattice <: de.tudarmstadt.consistency.store.objects.ConsistencyLattice[Consistency]

	type Var
	type Val

	type FieldName
	type MethodName
	type ClassName
}
