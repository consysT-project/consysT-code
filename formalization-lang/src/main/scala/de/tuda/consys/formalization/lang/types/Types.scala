package de.tuda.consys.formalization.lang.types

import de.tuda.consys.formalization.lang
import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.errors.TypeError
import de.tuda.consys.formalization.lang.{ArithmeticComparison, ArithmeticOperation, Block, BooleanCombination, BooleanValue, CallQuery, CallQueryThis, CallUpdate, CallUpdateThis, ClassDecl, ClassId, ConsistencyVarEnv, Default, EvalQuery, EvalUpdate, Expression, GetField, If, Let, LocalObj, Num, Print, Ref, Replicate, ReturnExpr, Sequence, SetField, Skip, Statement, Transaction, TypeVarEnv, TypeVarId, TypeVarMutabilityEnv, UnitLiteral, Var, While, topClassId}

import scala.annotation.tailrec

case class Type(l: ConsistencyType, m: MutabilityType, suffix: TypeSuffix) extends TypeLike[Type] {
    override def <=(t: Type)(implicit classTable: ClassTable,
                             typeVarEnv: TypeVarEnv,
                             typeVarMutabilityEnv: TypeVarMutabilityEnv,
                             consistencyVarEnv: ConsistencyVarEnv): Boolean = Subtyping.subtype(this, t)

    override def >=(t: Type)(implicit classTable: ClassTable,
                             typeVarEnv: TypeVarEnv,
                             typeVarMutabilityEnv: TypeVarMutabilityEnv,
                             consistencyVarEnv: ConsistencyVarEnv): Boolean = Subtyping.subtype(t, this)

    def withConsistency(l: ConsistencyType): Type = Type(l, m, suffix)
    def withMutability(m: MutabilityType): Type = Type(l, m, suffix)
    def withSuffix(suffix: TypeSuffix): Type = Type(l, m, suffix)

    override def toString: ClassId = s"[$l,$m]*$suffix"
}

sealed trait TypeSuffix

case class TypeSuffixVar(id: TypeVarId) extends TypeSuffix {
    override def toString: ClassId = s"$id"
}

case object BooleanTypeSuffix extends TypeSuffix

case object NumberTypeSuffix extends TypeSuffix

case object UnitTypeSuffix extends TypeSuffix

sealed trait NonVarTypeSuffix extends TypeSuffix

case class LocalTypeSuffix(classType: ClassType) extends NonVarTypeSuffix {
    override def toString: String = s"Val[$classType]"
}

case class RefTypeSuffix(classType: ClassType) extends NonVarTypeSuffix {
    override def toString: String = s"Ref[$classType]"
}

case class ClassType(classId: ClassId,
                     consistencyArguments: Seq[ConsistencyType],
                     typeArguments: Seq[TypeSuffix]) {
    override def toString: String =
        if (typeArguments.isEmpty & consistencyArguments.isEmpty) s"$classId"
        else s"$classId<${consistencyArguments.mkString(",")},${typeArguments.mkString(",")}>"
}

object Types {
    def bound(typ: Type)(implicit typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): Type =
        Type(bound(typ.l), typ.m, bound(typ.suffix))

    @tailrec
    def bound(typ: TypeSuffix)(implicit typeVars: TypeVarEnv): NonVarTypeSuffix = typ match {
        case TypeSuffixVar(id) =>
            typeVars.getOrElse(id, throw TypeError(s"cannot resolve type variable <$id>")) match {
                case t: TypeSuffixVar => bound(t) // allows recursive type variable bounds
                case t: NonVarTypeSuffix => t
            }

        case t: NonVarTypeSuffix => t
    }

    @tailrec
    def bound(typ: ConsistencyType)(implicit consistencyVars: ConsistencyVarEnv): ConcreteConsistencyType = typ match {
        case ConsistencyVar(name) =>
            consistencyVars.getOrElse(name, throw TypeError(s"cannot resolve consistency variable <$name>")) match {
                case t: ConsistencyVar => bound(t) // allows recursive type variable bounds
                case t: ConcreteConsistencyType => t
            }
        case t: ConcreteConsistencyType => t
    }

    def mBound(t: TypeSuffixVar)(implicit typeVarMutabilityEnv: TypeVarMutabilityEnv): MutabilityType =
        typeVarMutabilityEnv.getOrElse(t.id, throw TypeError(s"cannot resolve type variable <$t.id>"))

    def substitute(typ: Type, typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): Type =
        Type(substitute(typ.l, consistencyVars), typ.m, substitute(typ.suffix, typeVars, consistencyVars))

    def substitute(typ: TypeSuffix, typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): TypeSuffix = typ match {
        case TypeSuffixVar(id) => typeVars.get(id) match {
            case Some(value) => value
            case None => TypeSuffixVar(id)
        }
        case RefTypeSuffix(classType) => RefTypeSuffix(substitute(classType, typeVars, consistencyVars))
        case LocalTypeSuffix(classType) => LocalTypeSuffix(substitute(classType, typeVars, consistencyVars))
        case x => x
    }

    def substitute(typ: ClassType, typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): ClassType =
        ClassType(typ.classId,
            typ.consistencyArguments.map(t => substitute(t, consistencyVars)),
            typ.typeArguments.map(t => substitute(t, typeVars, consistencyVars)))

    def substitute(typ: ConsistencyType, consistencyVars: ConsistencyVarEnv): ConsistencyType = typ match {
        case consistencyType: ConcreteConsistencyType => consistencyType
        case ConsistencyUnion(t1, t2) => ConsistencyUnion(substitute(t1, consistencyVars), substitute(t2, consistencyVars))
        case ConsistencyVar(name) => consistencyVars.get(name) match {
            case Some(value) => value
            case None => ConsistencyVar(name)
        }
    }

    def substitute(expr: Expression, typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): Expression = expr match {
        case Ref(id, classType) =>
            Ref(id, substitute(classType, typeVars, consistencyVars))
        case LocalObj(classType, constructor) =>
            LocalObj(substitute(classType, typeVars, consistencyVars), constructor.map(f => f._1 -> substitute(f._2, typeVars, consistencyVars)))
        case Default(s, l, m) =>
            Default(substitute(s, typeVars, consistencyVars), substitute(l, consistencyVars), m)
        case ArithmeticOperation(e1, e2, op) =>
            ArithmeticOperation(substitute(e1, typeVars, consistencyVars), substitute(e2, typeVars, consistencyVars), op)
        case ArithmeticComparison(e1, e2, op) =>
            ArithmeticComparison(substitute(e1, typeVars, consistencyVars), substitute(e2, typeVars, consistencyVars), op)
        case BooleanCombination(e1, e2, op) =>
            BooleanCombination(substitute(e1, typeVars, consistencyVars), substitute(e2, typeVars, consistencyVars), op)
        case x => x
    }

    def substitute(stmt: Statement, typeVars: TypeVarEnv, consistencyVars: ConsistencyVarEnv): Statement = stmt match {
        case ReturnExpr(e) => ReturnExpr(substitute(e, typeVars, consistencyVars))
        case Block(vars, s) =>
            Block(vars.map(v => (substitute(v._1, typeVars, consistencyVars), v._2, substitute(v._3, typeVars, consistencyVars))), substitute(s, typeVars, consistencyVars))
        case Sequence(s1, s2) =>
            Sequence(substitute(s1, typeVars, consistencyVars), substitute(s2, typeVars, consistencyVars))
        case If(conditionExpr, thenStmt, elseStmt) =>
            If(substitute(conditionExpr, typeVars, consistencyVars), substitute(thenStmt, typeVars, consistencyVars), substitute(elseStmt, typeVars, consistencyVars))
        case While(condition, stmt) =>
            While(substitute(condition, typeVars, consistencyVars), substitute(stmt, typeVars, consistencyVars))
        case Let(varId, e) =>
            Let(varId, substitute(e, typeVars, consistencyVars))
        case SetField(fieldId, valueExpr) =>
            SetField(fieldId, substitute(valueExpr, typeVars, consistencyVars))
        case CallUpdate(recvExpr, methodId, argumentExprs) =>
            CallUpdate(substitute(recvExpr, typeVars, consistencyVars), methodId, argumentExprs.map(substitute(_, typeVars, consistencyVars)))
        case CallUpdateThis(methodId, argumentExprs) =>
            CallUpdateThis(methodId, argumentExprs.map(substitute(_, typeVars, consistencyVars)))
        case EvalUpdate(recv, methodId, args, body) =>
            EvalUpdate(substitute(recv, typeVars, consistencyVars), methodId, args.map(a => (a._1, substitute(a._2, typeVars, consistencyVars))), body)
        case CallQuery(varId, recvExpr, methodId, argumentExprs) =>
            CallQuery(varId, substitute(recvExpr, typeVars, consistencyVars), methodId, argumentExprs.map(substitute(_, typeVars, consistencyVars)))
        case CallQueryThis(varId, methodId, argumentExprs) =>
            CallQueryThis(varId, methodId, argumentExprs.map(substitute(_, typeVars, consistencyVars)))
        case EvalQuery(varId, recv, methodId, args, body) =>
            EvalQuery(varId, substitute(recv, typeVars, consistencyVars), methodId, args.map(a => (a._1, substitute(a._2, typeVars, consistencyVars))), body)
        case Replicate(varId, refId, classType, constructor) =>
            Replicate(varId, refId, substitute(classType, typeVars, consistencyVars), constructor.map(c => (c._1, substitute(c._2, typeVars, consistencyVars))))
        case Transaction(body, except) =>
            Transaction(substitute(body, typeVars, consistencyVars), substitute(except, typeVars, consistencyVars))
        case Print(expression) =>
            Print(substitute(expression, typeVars, consistencyVars))
        case x => x
    }

    def wellFormed(typ: Type)
                  (implicit classTable: ClassTable,
                   tvEnv: TypeVarEnv,
                   tvmEnv: TypeVarMutabilityEnv,
                   cvEnv: ConsistencyVarEnv
                  ): Boolean = {
        wellFormed(typ.suffix, typ.m) && wellFormed(typ.l)
    }

    def wellFormed(suffix: TypeSuffix, m: MutabilityType)
                  (implicit classTable: ClassTable,
                   tvEnv: TypeVarEnv,
                   tvmEnv: TypeVarMutabilityEnv,
                   cvEnv: ConsistencyVarEnv,
                  ): Boolean = suffix match {
        case TypeSuffixVar(id) => tvEnv.contains(id) && Subtyping.subtype(tvmEnv(id), m)
        case RefTypeSuffix(classType) => wellFormed(classType)
        case LocalTypeSuffix(classType) => wellFormed(classType)
        case BooleanTypeSuffix => true
        case NumberTypeSuffix => true
        case UnitTypeSuffix => true
    }

    def wellFormed(classType: ClassType)
                  (implicit classTable: ClassTable,
                   tvEnv: TypeVarEnv,
                   tvmEnv: TypeVarMutabilityEnv,
                   cvEnv: ConsistencyVarEnv
                  ): Boolean = classType match {
        case ClassType(id, Nil, Nil) if id == topClassId => true
        case ClassType(classId, consistencyArguments, typeArguments) => classTable.get(classId) match {
            case Some(ClassDecl(_, consistencyParameters, typeParameters, _, _, _)) =>
                consistencyParameters.size == consistencyArguments.size &&
                  consistencyArguments.forall(wellFormed) &&
                  (consistencyArguments zip consistencyParameters.map(_.upperBound)).forall(p => p._1 <= p._2) &&
                  typeParameters.size == typeArguments.size &&
                  (typeArguments zip typeParameters).forall(p => wellFormed(p._1, p._2.mBound)) &&
                  (typeArguments zip typeParameters).forall(p => Subtyping.subtype(p._2.mBound, p._1, p._2.upperBound))
            case None => false
        }
    }

    def wellFormed(l: ConsistencyType)(implicit cvEnv: ConsistencyVarEnv): Boolean = l match {
        case _: ConcreteConsistencyType => true
        case ConsistencyUnion(t1, t2) => wellFormed(t1) && wellFormed(t2)
        case ConsistencyVar(name) => cvEnv.contains(name)
    }

    def booleanType: Type = Type(Local, Immutable, BooleanTypeSuffix)

    def booleanType(c: ConsistencyType): Type = Type(c, Immutable, BooleanTypeSuffix)

    def numberType: Type = Type(Local, Immutable, NumberTypeSuffix)

    def numberType(c: ConsistencyType): Type = Type(c, Immutable, NumberTypeSuffix)

    def unitType: Type = Type(Local, Immutable, UnitTypeSuffix)

    def unitType(c: ConsistencyType): Type = Type(c, Immutable, UnitTypeSuffix)

    def localType(classType: ClassType): Type = Type(Local, Immutable, LocalTypeSuffix(classType))

    def localType(c: ConsistencyType, classType: ClassType): Type = Type(c, Immutable, LocalTypeSuffix(classType))

    def refType(classType: ClassType): Type = Type(Local, Mutable, RefTypeSuffix(classType))

    def refType(c: ConsistencyType, classType: ClassType): Type = Type(c, Mutable, RefTypeSuffix(classType))

    def refType(c: ConsistencyType, m: MutabilityType, classType: ClassType): Type = Type(c, m, RefTypeSuffix(classType))
}