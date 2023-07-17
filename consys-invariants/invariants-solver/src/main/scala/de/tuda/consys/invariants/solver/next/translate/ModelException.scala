package de.tuda.consys.invariants.solver.next.translate

import de.tuda.consys.invariants.solver.next.ir.Classes.Type

class ModelException(msg : String) extends Exception(msg)

class UnknownTypeModelException(typ : Type) extends ModelException("unknown type: " + typ)
