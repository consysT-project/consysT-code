package de.tuda.consys.invariants.solver.next.translate

import de.tuda.consys.invariants.solver.next.ir.IR.IRType

class ModelException(msg : String) extends Exception(msg)

class UnknownTypeModelException(typ : IRType) extends ModelException("unknown type: " + typ)
