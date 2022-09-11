package de.tuda.stg.consys.invariants.lang.solver

import com.microsoft.z3.{ArithSort, DatatypeSort, FuncDecl, Sort, TupleSort, Context => Z3Context, Expr => Z3Expr}
import de.tuda.stg.consys.invariants.lang.solver.ClassTableTranslator.{ClassModel, Z3ClassTable}
import de.tuda.stg.consys.invariants.lang.{ClassDef, ClassId, ClassTable, FieldId}


trait ClassTableTranslator { this : BaseTranslator with TypeTranslator =>

  def translateClass(clsDef : ClassDef) : ClassModel = {
    val clsName = context.mkSymbol(clsDef.name)

    val (fieldSymbols, fieldSorts) = clsDef.fields.map(f => (context.mkSymbol(f.name), translateType(f.typ))).unzip

    val classSort = context.mkTupleSort(clsName,
      fieldSymbols.toArray, fieldSorts.toArray
    )

    ClassModel(classSort)
  }

  def translateClassTable(ct : ClassTable) : ClassTable with Z3ClassTable = {

    val modelMap = ct.classes.map(clsDef => (clsDef.name, translateClass(clsDef))).toMap

    new ClassTable(ct.classes : _*) with Z3ClassTable {
      override def models : Map[ClassId, ClassModel] = modelMap
    }
  }
}

object ClassTableTranslator {
  case class ClassModel(classSort : TupleSort) {
    def getSort : TupleSort = classSort

    def fieldSelector(f : FieldId) : Option[FuncDecl[_]] =
      classSort.getFieldDecls.find(decl => decl.getName.toString == f)
  }


  trait Z3ClassTable { this : ClassTable =>
    def models : Map[ClassId, ClassModel]
  }

}
