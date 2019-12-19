package de.tuda.stg.consys


/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
package object core {




	implicit def refToRob[Addr, T <: AnyRef](ref : Ref[Addr, T]) : ReplicatedObject[Addr, T] =
		ref.deref
}
