package de.tudarmstadt.consistency.replobj.actors

import de.tudarmstadt.consistency.replobj.actors.Context.ContextPath

import scala.util.Random

/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
object Requests {

	trait Request {	def returns : Boolean }
	trait ReturnRequest { self : Request =>	override def returns : Boolean = true }
	trait NonReturnRequest { self : Request => override def returns : Boolean = false}

	sealed trait LocalReq extends Request
	case class OpReq(op : Operation[_]) extends LocalReq with ReturnRequest
	case object SyncReq extends LocalReq with ReturnRequest


	sealed trait Operation[+R] {
		def id : ContextPath
	}
	case class GetFieldOp[+R](id : ContextPath, fldName : String) extends Operation[R]
	case class SetFieldOp(id : ContextPath, fldName : String, newVal : Any) extends Operation[Unit]
	case class InvokeOp[+R](id : ContextPath, mthdName : String, args : Seq[Any]) extends Operation[R]


}
