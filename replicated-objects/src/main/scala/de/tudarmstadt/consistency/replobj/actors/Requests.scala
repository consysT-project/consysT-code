package de.tudarmstadt.consistency.replobj.actors



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
		def path : ContextPath
	}
	case class GetFieldOp[+R](path : ContextPath, fldName : String) extends Operation[R]
	case class SetFieldOp(path : ContextPath, fldName : String, newVal : Any) extends Operation[Unit]
	case class InvokeOp[+R](path : ContextPath, mthdName : String, args : Seq[Any]) extends Operation[R]


}
