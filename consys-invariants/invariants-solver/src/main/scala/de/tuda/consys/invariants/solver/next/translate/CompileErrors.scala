package de.tuda.consys.invariants.solver.next.translate

import de.tuda.consys.invariants.solver.next.ir.Classes.{ClassId, FieldId, MethodId, VarId}


object CompileErrors {

  class CompileException(msg : String = "error") extends Exception(msg)

  def classNotFound(classId : ClassId) : Nothing =
    throw new CompileException(s"class not found: $classId")

  def fieldNotFound(classId: ClassId, fieldId: FieldId) : Nothing =
    throw new CompileException(s"field not found: $fieldId (in class $classId)")

  def methodNotFound(classId : ClassId, methodId: MethodId) =
    throw new CompileException(s"method not found: $methodId (in class $classId)")

  def varNotFound(varId : VarId) =
    throw new CompileException(s"variable not found: $varId")

}
