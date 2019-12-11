package de.tuda.stg.consys.experimental.lang.store

/**
 * Created on 10.12.19.
 *
 * @author Mirko Köhler
 */
trait Handler[T] {

	def invoke[R](methodId : String, args : Seq[Seq[Any]]) : R

}
