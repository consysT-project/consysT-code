package de.tuda.consys.formalization.lang.errors

case class TypeError(message: String) extends Exception(message)
