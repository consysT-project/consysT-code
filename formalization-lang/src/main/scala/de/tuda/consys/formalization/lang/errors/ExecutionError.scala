package de.tuda.consys.formalization.lang.errors

case class ExecutionError(message: String) extends Exception(message)
