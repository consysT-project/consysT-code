package de.tuda.stg.consys.invariants.lang

import de.tuda.stg.consys.invariants.lang.Program.Tx
import de.tuda.stg.consys.invariants.lang.ast.Statement


case class ClassTable(classes : ClassDef*) {

	private lazy val index : Map[ClassId, ClassDef] =
		classes.map(cls => (cls.name, cls)).toMap

	def getOrElse[B >: ClassDef](c : ClassId, orElse : => B) : B =
		index.getOrElse(c, orElse)

	def apply(c : ClassId) : ClassDef = index(c)

	def add(clsDef : ClassDef) : ClassTable =
		ClassTable((classes :+ clsDef) : _*)

}

object ClassTable {

	private var globalTable : ClassTable = ClassTable()

	def define(cls : ClassDef) : Unit =
		globalTable = globalTable.add(cls)

	def start(stmts : Statement*) : Program =
		Program(globalTable, stmts.map(stmt => Tx(stmt)) : _*)


}
