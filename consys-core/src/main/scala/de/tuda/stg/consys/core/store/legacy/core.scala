package de.tuda.stg.consys.core.store

import scala.language.implicitConversions


/**
 * Created on 26.11.19.
 *
 * @author Mirko Köhler
 */
package object legacy {
	implicit def refToRob[Addr, T <: AnyRef](ref : Ref[Addr, T]) : ReplicatedObject[Addr, T] =
		ref.deref
}
