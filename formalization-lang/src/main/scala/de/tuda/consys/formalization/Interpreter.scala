package de.tuda.consys.formalization

import de.tuda.consys.formalization.Interpreter._
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.types._
import de.tuda.consys.formalization.lang.ClassTable.ClassTable
import de.tuda.consys.formalization.lang.errors.ExecutionError
import de.tuda.stg.consys.core.store.ConsistencyLevel
import de.tuda.stg.consys.core.store.cassandra.{CassandraStore, CassandraTransactionContext}

class Interpreter(storeAddress: String) {
    private type VarEnv = Map[VarId, Value]

    private val store = CassandraStore.fromAddress(storeAddress, 9042, 2181, "datacenter1", initialize = true)

    def run(programDecl: ProgramDecl): Value = {
        val r1 = interpret(programDecl.body, Map.empty)(programDecl.classTable, None)
        val r2 = interpret(programDecl.returnExpr, r1)(programDecl.classTable, None)
        store.close()
        r2
    }

    private def interpret(stmt: Statement, varEnv: VarEnv)
                         (implicit classTable: ClassTable, transaction: Option[CassandraTransactionContext]): VarEnv = stmt match {
        case Sequence(s1, s2) =>
            val r1 = interpret(s1, varEnv)
            interpret(s2, r1)

        case If(conditionExpr, thenStmt, elseStmt) =>
            interpret(conditionExpr, varEnv) match {
                case BoolV(b) =>
                    if (b) interpret(thenStmt, varEnv)
                    else interpret(elseStmt, varEnv)
                    varEnv

                case _ => throw ExecutionError("wrong condition value")
            }

        case Let(varId, rhs) =>
            val r = interpret(rhs, varEnv)
            varEnv + (varId -> r)

        case Assign(varId, rhs) =>
            val r = interpret(rhs, varEnv)
            varEnv + (varId -> r)

        case SetField(fieldId, valueExpr) => transaction match {
            case Some(ctx) =>
                varEnv(thisId) match {
                    case RefV(objectId, _, _) =>
                        // TODO
                        val (ref, fields) = getReplicatedFields(objectId, consistency, ctx)

                        val value = interpret(valueExpr, varEnv)
                        ref.resolve(ctx).setField("fields", fields.updated(fieldId, value))

                    case _ => throw RuntimeError("invalid value for <this>")
                }
            case None => throw RuntimeError("missing transaction for <GetField>")
        }

        case CallUpdate(recvExpr, methodId, argumentExprs) => ???

        case Transaction(body, except) =>
            val result = store.transaction(ctx =>
                Some(interpret(body, varEnv)(classTable, Some(ctx)))
            )
            result match {
                case Some(_) => varEnv
                case None => interpret(except, varEnv)
            }
    }

    private def interpret(rhs: AssignRhs, varEnv: VarEnv)
                         (implicit classTable: ClassTable, transaction: Option[CassandraTransactionContext]): Value = rhs match {
        case rhsExpression(e) =>
            interpret(e, varEnv)

        case rhsGetField(fieldId) => ???
        case rhsCallQuery(recvExpr, methodId, argumentExprs) => ???
        case rhsReplicate(location, classId, consistencyArguments, typeArguments, constructor, consistency, mutability) => ???
        case rhsLookup(location, classId, consistencyArguments, typeArguments, consistency, mutability) => ???
    }

    private def interpret(expr: Expression, varEnv: VarEnv)
                         (implicit classTable: ClassTable, transaction: Option[CassandraTransactionContext]): Value = expr match {
        case Num(n) => NumV(n)

        case True => BoolV(true)

        case False => BoolV(false)

        case UnitLiteral => UnitV

        case This => varEnv(thisId)

        case Var(id) => varEnv(id)

        case Equals(expr1, expr2) =>
            (interpret(expr1, varEnv), interpret(expr2, varEnv)) match {
                case (NumV(n1), NumV(n2)) => BoolV(n1 == n2)
                case (BoolV(b1), BoolV(b2)) => BoolV(b1 == b2)
                case (RefV(id1, _, _), RefV(id2, _, _)) => BoolV(id1 == id2)
                case (UnitV, UnitV) => BoolV(true)
                case _ => BoolV(false)
            }

        case Add(expr1, expr2) =>
            (interpret(expr1, varEnv), interpret(expr2, varEnv)) match {
                case (NumV(n1), NumV(n2)) => NumV(n1 + n2)
                case (a, b) => throw RuntimeError(s"invalid operands for <Add>: $a, $b")
            }

        case New(objectId, classId, typeArguments, consistency, constructorExprs) =>
            // TODO: should we keep class info erased?
            transaction match {
                case Some(ctx) =>
                    val constructorValues = constructorExprs.map(entry => {
                        entry._1 -> interpret(entry._2, varEnv)
                    })
                    ctx.replicate[ReplicatedState](objectId, runtimeConsistency(consistency), objectId, consistency, constructorValues)
                    RefV(objectId, classId, consistency)

                case None => throw RuntimeError("<New> outside of transaction")
            }

        case GetField(fieldId) => transaction match {
            case Some(ctx) =>
                varEnv(thisId) match {
                    case RefV(objectId, _, consistency) =>
                        // TODO: use method consistency instead of ref consistency to properly model mixed refs
                        val (_, fields) = getReplicatedFields(objectId, consistency, ctx)
                        fields(fieldId)

                    case _ => throw RuntimeError("invalid value for <this>")
                }

            case None => throw RuntimeError("<GetField> outside of transaction")
        }

        case SetField(fieldId, valueExpr) =>

        case CallQuery(recvExpr, methodId, argumentExprs) => transaction match {
            case Some(ctx) =>
                val recvValue = interpret(recvExpr, varEnv)
                recvValue match {
                    case ref@RefV(objectId, classId, consistency) =>
                        val classDecl = classTable.getOrElse((classId, consistency),
                            throw RuntimeError(s"unknown class: $consistency $classId"))
                        val methodDecl = classDecl.getMethodWithSuperclass(methodId).getOrElse(
                            throw RuntimeError(s"unknown method: $methodId (in class $classId)"))

                        // Force read of object with appropriate consistency to mimic invoke
                        ctx.lookup[ReplicatedState](objectId, runtimeConsistency(methodDecl.operationLevel.consistencyType()))

                        val newVarEnv = (methodDecl.declaredParameterNames zip argumentExprs).
                            foldLeft(varEnv)((env, paramArg) => env + (paramArg._1 -> interpret(paramArg._2, varEnv)))
                        interpret(methodDecl.body, newVarEnv + (thisId -> ref))

                    case _ => throw RuntimeError("invalid value for receiver")
                }

            case None => throw RuntimeError("<GetField> outside of transaction")
        }

        case CallUpdate(recvExpr, methodId, argumentExprs) => transaction match {
            case Some(ctx) =>
                val recvValue = interpret(recvExpr, varEnv)
                recvValue match {
                    case ref@RefV(objectId, classId, consistency) =>
                        val classDecl = classTable.getOrElse((classId, consistency),
                            throw RuntimeError(s"unknown class: $consistency $classId"))
                        val methodDecl = classDecl.getMethodWithSuperclass(methodId).getOrElse(
                            throw RuntimeError(s"unknown method: $methodId (in class $classId)"))

                        // Force read of object with appropriate consistency to mimic invoke
                        ctx.lookup[ReplicatedState](objectId, runtimeConsistency(methodDecl.operationLevel.consistencyType()))

                        val newVarEnv = (methodDecl.declaredParameterNames zip argumentExprs).
                            foldLeft(varEnv)((env, paramArg) => env + (paramArg._1 -> interpret(paramArg._2, varEnv)))
                        interpret(methodDecl.body, newVarEnv + (thisId -> ref))

                        UnitV

                    case _ => throw RuntimeError("invalid value for receiver")
                }

            case None => throw RuntimeError("<GetField> outside of transaction")
        }
    }

    private def runtimeConsistency(consistencyType: ConsistencyType): ConsistencyLevel[CassandraStore] = consistencyType match {
        case Strong => de.tuda.stg.consys.core.store.cassandra.levels.Strong
        case Mixed => de.tuda.stg.consys.core.store.cassandra.levels.Mixed
        case Weak => de.tuda.stg.consys.core.store.cassandra.levels.Weak
        case l => throw RuntimeError(s"invalid consistency level: $l")
    }

    private def getReplicatedFields(objectId: String,
                                    consistency: ConsistencyType,
                                    ctx: CassandraTransactionContext): (CassandraStore#RefType[ReplicatedState], Map[FieldId, Value]) = {
        val ref = ctx.lookup[ReplicatedState](objectId, runtimeConsistency(consistency))
        val fields = ref.resolve(ctx).getField[Map[FieldId, Value]]("fields")
        (ref, fields)
    }
}

object Interpreter {
    case class RuntimeError(message: String) extends Exception(message)

    private class ReplicatedState(var objectId: String,
                                  var consistency: ConsistencyType,
                                  var fields: Map[FieldId, Value]
                                 ) extends Serializable
}
