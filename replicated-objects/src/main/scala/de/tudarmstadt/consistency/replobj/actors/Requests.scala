package de.tudarmstadt.consistency.replobj.actors

import akka.actor.ActorRef
import akka.util.Timeout

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps


/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
object Requests {

	trait Request {	def returns : Boolean }
	trait ReturnRequest { self : Request =>	override def returns : Boolean = true }
	trait NonReturnRequest { self : Request => override def returns : Boolean = false}


	sealed trait Operation[+R] {
		//The transaction in which the operation happens
		def tx : Transaction
	}
	case class GetFieldOp[+R](tx : Transaction, fldName : String) extends Operation[R]
	case class SetFieldOp(tx : Transaction, fldName : String, newVal : Any) extends Operation[Unit]
	case class InvokeOp[+R](tx : Transaction, mthdName : String, args : Seq[Any]) extends Operation[R]



	trait RequestHandler[Addr] {
		def request(addr : Addr, req : Request, receiveTimeout : FiniteDuration = 30 seconds) : Any
		def close() : Unit
	}

	case object InitHandler
	case class HandleRequest[Addr](addr : Addr, request : Request)
	case object CloseHandler

	@SerialVersionUID(42947104L)
	class RequestHandlerImpl[Addr](private val requestActor : ActorRef) extends RequestHandler[Addr] with Serializable {
		requestActor ! InitHandler

		override def request(addr : Addr, req : Request, receiveTimeout : FiniteDuration = 30 seconds) : Any = {
			if (req.returns) {
				import akka.pattern.ask
				val response = requestActor.ask(HandleRequest(addr, req))(Timeout(receiveTimeout))
				val result = Await.result(response, receiveTimeout)
				result
			} else {
				requestActor ! HandleRequest(addr, req)
			}
		}

		override def close() : Unit = {
			requestActor ! CloseHandler
		}
	}


}
