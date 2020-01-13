package de.tuda.stg.consys.core.store

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait Handler[T] {

	def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R

}
