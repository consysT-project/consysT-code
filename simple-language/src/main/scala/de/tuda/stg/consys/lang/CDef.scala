package de.tuda.stg.consys.lang

import de.tuda.stg.consys.lang.CDef.{FDef, MDef}

/**
	* Created on 04.07.19.
	*
	* @author Mirko Köhler
	*/
case class CDef(name : ClassName, parentName : ClassName, fields : Seq[FDef], methods : Seq[MDef])

object CDef {
	case class FDef(typ : Type, name : FieldName)
	case class MDef(returnTyp : Type, methodName : MethodName, parameters : Seq[PDef], body : Computation, ret : Expression)
	case class PDef(typ : Type, name : VarName)
}