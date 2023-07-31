package de.tuda.consys.invariants.solver.next.translate

import com.microsoft.z3.Sort
import de.tuda.consys.invariants.solver.next.ir.Classes._
import de.tuda.consys.invariants.solver.next.ir.Types.{ClassType, Type, TypeVar}
import de.tuda.consys.invariants.solver.next.translate.RepTable.{FieldRep, InstantiatedNativeClassRep, InstantiatedObjectClassRep, MethodRep, ParametrizedClassRep, ParametrizedNativeClassRep, ParametrizedObjectClassRep}
import de.tuda.consys.invariants.solver.next.translate.Z3Representations.CachedMap

import scala.collection.mutable

class RepMapBuilder {
  // Maps the class ids of object classes to their sorts and fields
  private val objectClassMap = mutable.Map.empty[ClassId, CachedMap[Seq[Sort], (Sort, Map[FieldId, FieldRep])]]
  // Maps the class ids of native classes to their sorts
  private val nativeClassMap = mutable.Map.empty[ClassId, CachedMap[Seq[Sort], Sort]]
  // Maps class and method ids to their method representations
  private val methodMap = mutable.Map.empty[ClassId, mutable.Map[MethodId, CachedMap[Seq[Sort], MethodRep]]]


  def addNativeClassBuilder(classId : ClassId, repBuilder : Seq[Sort] => Sort) : Unit =
    nativeClassMap.put(classId, new CachedMap[Seq[Sort], Sort](repBuilder))

  def addObjectClassBuilder(classId : ClassId, repBuilder : Seq[Sort] => (Sort, Map[FieldId, FieldRep])) : Unit =
    objectClassMap.put(classId, new CachedMap[Seq[Sort], (Sort, Map[FieldId, FieldRep])](repBuilder))

  def addMethodBuilder(classId : ClassId, methodId : MethodId, repBuilder : Seq[Sort] => MethodRep) : Unit = {
    methodMap.getOrElseUpdate(classId, mutable.Map.empty)
      .put(methodId, new CachedMap[Seq[Sort], MethodRep](repBuilder))
  }

  def getClassSort(classId : ClassId, typeArguments : Seq[Sort]) : Option[Sort] = {
    nativeClassMap.get(classId) match {
      case None => objectClassMap.get(classId).map(f => f(typeArguments)._1)
      case Some(f) => Some(f(typeArguments))
    }
  }

  def getField(classId : ClassId, typeArguments : Seq[Sort], fieldId : FieldId) : Option[FieldRep] = {
    objectClassMap.get(classId) match {
      case None => None
      case Some(f) => f(typeArguments)._2.get(fieldId)
    }
  }

  def getMethod(classId : ClassId, typeArguments : Seq[Sort], methodId : MethodId) : Option[MethodRep] = {
    methodMap.get(classId) match {
      case None => None
      case Some(methodMap) =>
        methodMap.get(methodId) match {
          case None => None
          case Some(f) => Some(f(typeArguments))
        }
    }
  }

//  def getClassRep(classId : ClassId, typeArguments : Seq[Sort]) : Option[InstantiatedClassRep] = {
//    objectClassMap.get(classId) match {
//      case None => None
//      case Some(f) =>
//        val (sort, fields) = f.apply(typeArguments)
//        val methodMapBuilder = Map.newBuilder[MethodId, MethodRep]
//        val classDecl = classTable.getOrElse(classId, return None)
//        for (methodDecl <- classDecl.methods.values) {
//          val methodRepBuilder = methodMap.getOrElse((classId, methodDecl.name), return None)
//          methodMapBuilder.addOne(methodDecl.name, methodRepBuilder(Seq[Sort]))
//        }
//        Some(new InstantiatedObjectClassRep(
//          sort, fields, methodMapBuilder.result()
//        ))
//    }
//  }

  def resolveType(typ : Type, typeVarSorts : Map[TypeVarId, Sort]) : Sort = typ match {
    case TypeVar(typeVarId) => typeVarSorts.getOrElse(typeVarId, throw new ModelException("type var not available: " + typeVarId))
    case ClassType(classId, typeArguments) =>
      val typArgSorts = typeArguments.map(t => resolveType(t, typeVarSorts))
      val fieldSort = getClassSort(classId, typArgSorts).getOrElse(throw new ModelException("class not available: " + classId))
      fieldSort
  }

  def result() : RepTable = {
    val tableBuilder = Map.newBuilder[ClassId, ParametrizedClassRep[_]]

    for ((classId, classRep) <- objectClassMap) {
      val instances : Seq[Sort] => InstantiatedObjectClassRep = sorts => {
        val (classSort, fieldReps) = classRep(sorts)

        val methodsBuilder = Map.newBuilder[MethodId, MethodRep]
        val methodsOfClass = methodMap.getOrElse(classId, mutable.Map.empty)
        for ((methodId, methodReps) <- methodsOfClass) {
          methodsBuilder.addOne((methodId, methodReps(sorts)))
        }

        new InstantiatedObjectClassRep(
          classSort,
          fieldReps,
          methodsBuilder.result()
        )
      }

      val objectClassRep = new ParametrizedObjectClassRep(new CachedMap(instances))
      tableBuilder.addOne(classId, objectClassRep)
    }

    for ((classId, classRep) <- nativeClassMap) {
      val instances : Seq[Sort] => InstantiatedNativeClassRep = sorts => {
        val classSort = classRep(sorts)

        val methodsBuilder = Map.newBuilder[MethodId, MethodRep]
        val methodsOfClass = methodMap.getOrElse(classId, mutable.Map.empty)
        for ((methodId, methodReps) <- methodsOfClass) {
          methodsBuilder.addOne((methodId, methodReps(sorts)))
        }

        new InstantiatedNativeClassRep(
          classSort,
          methodsBuilder.result()
        )
      }

      val nativeClassRep = new ParametrizedNativeClassRep(new CachedMap(instances))
      tableBuilder.addOne(classId, nativeClassRep)
    }

    new RepTable(tableBuilder.result())
  }

}
