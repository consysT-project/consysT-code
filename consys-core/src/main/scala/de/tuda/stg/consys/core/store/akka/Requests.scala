package de.tuda.stg.consys.core.store.akka

import akka.actor.ActorRef
import akka.util.Timeout

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}
import scala.language.postfixOps


/**
	* Created on 12.03.19.
	*
	* @author Mirko Köhler
	*/
object Requests {

	sealed trait Request[T]
	trait SynchronousRequest[T] extends Request[T]
	trait AsynchronousRequest[T] extends Request[Future[T]]
	trait NoAnswerRequest extends Request[Unit]



	sealed trait Operation[+R] {
		//The transaction in which the operation happens
		def tx : String
	}
	case class GetFieldOp[+R](tx : String, fldName : String) extends Operation[R]
	case class SetFieldOp(tx : String, fldName : String, newVal : Any) extends Operation[Unit]
	case class InvokeOp[+R](tx : String, mthdName : String, args : Seq[Seq[Any]]) extends Operation[R]



	trait RequestHandler[Addr] extends AutoCloseable {
		def request[R](addr : Addr, req : Request[R]) : R
	}

	case object InitHandler
	case class HandleRequest[Addr](addr : Addr, request : Request[_])
	case object CloseHandler


	class RequestHandlerImpl[Addr](private val requestActor : ActorRef, val defaultTimeout : FiniteDuration) extends RequestHandler[Addr] with Serializable {
		requestActor ! InitHandler

		override def request[R](addr : Addr, req : Request[R]) : R = req match {
			case syncReq : SynchronousRequest[_] =>
				import akka.pattern.ask
				val response = requestActor.ask(HandleRequest(addr, req))(Timeout(defaultTimeout))
				val result = Await.result(response, defaultTimeout)
				result.asInstanceOf[R]

			case asyncReq : AsynchronousRequest[_] =>
				import akka.pattern.ask
				val response = requestActor.ask(HandleRequest(addr, req))(Timeout(defaultTimeout))
				response.asInstanceOf[R]

			case noAnsReq : NoAnswerRequest =>
				requestActor ! HandleRequest(addr, req)
				().asInstanceOf[R]
		}


		override def close() : Unit = {
			requestActor ! CloseHandler
		}
	}


}
