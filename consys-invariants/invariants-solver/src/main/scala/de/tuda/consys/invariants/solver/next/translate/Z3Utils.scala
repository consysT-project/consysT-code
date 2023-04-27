package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.{DatatypeSort, Expr, FuncDecl, Sort}
import de.tuda.consys.invariants.solver.next.ir.IR.FieldId

object Z3Utils {


	type ObjectSort = DatatypeSort[_]

	def isObjectSort(sort : Sort) : Boolean = {
		sort match {
			case objSort : DatatypeSort[_] => objSort.getNumConstructors == 1
			case _ => false
		}
	}

	def asObjectSort(sort : Sort) : Option[ObjectSort] = {
		if (isObjectSort(sort)) Some(sort.asInstanceOf[ObjectSort]) else None
	}

	def getObjectConstructor(sort : ObjectSort) : FuncDecl[ObjectSort] = {
		require(isObjectSort(sort))
		sort.getConstructors.apply(0).asInstanceOf[FuncDecl[ObjectSort]]
	}

	def getObjectFields(sort : ObjectSort) : Array[FuncDecl[_]] = {
		require(isObjectSort(sort))
		sort.getAccessors.apply(0)
	}

	def getObjectField(sort : ObjectSort, name : String) : Option[FuncDecl[_]] = {
		require(isObjectSort(sort))
		sort.getAccessors.apply(0).find(decl => decl.getName.toString == name)
	}


}
