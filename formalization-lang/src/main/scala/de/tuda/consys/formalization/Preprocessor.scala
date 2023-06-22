package de.tuda.consys.formalization

import de.tuda.consys.formalization.lang._

// TODO: add PolyConsistent substitution
object Preprocessor {
    def process(programDecl: ProgramDecl): ProgramDecl = {
        val newClassTable = programDecl.classTable.map(entry => {
            val ((classId, consistency), classDecl) = entry
            ((classId, consistency), processClass(classDecl, consistency))
        })
        ProgramDecl(newClassTable, programDecl.body)
    }

    private def processClass(classDecl: ClassDecl, thisType: ConsistencyType): ClassDecl = {
        thisType match {
            case Local => processNonMixed(classDecl, Local)
            case Strong => processNonMixed(classDecl, Strong)
            case Weak => processNonMixed(classDecl, Weak)
            case Inconsistent => processNonMixed(classDecl, Inconsistent)
            case Mixed => processMixed(classDecl)
        }
    }

    private def processNonMixed(classDecl: ClassDecl, thisType: ConsistencyType): ClassDecl = {
        val newMethods = classDecl.methods.map(entry => {
            val (id, decl) = entry
            val newDecl = decl match {
                case QueryMethodDecl(name, _, declaredParameters, returnTyp, body) =>
                    QueryMethodDecl(name, thisType.operationLevel(), declaredParameters, returnTyp, body)

                case UpdateMethodDecl(name, _, declaredParameters, body) =>
                    UpdateMethodDecl(name, thisType.operationLevel(), declaredParameters, body)
            }

            (id, newDecl)
        })

        val newFields = classDecl.fields.map(f => {
            val (id, FieldDecl(fid, typ)) = f
            val newType = typ match {
                case CompoundType(baseType, _, mutabilityType) =>
                    CompoundType(baseType, thisType, mutabilityType)

                case TypeVar(typeVarId, upperBound) => ???
            }

            (id,  lang.FieldDecl(fid, newType))
        })

        classDecl.copy(methods = newMethods, fields = newFields)
    }

    private def processMixed(classDecl: ClassDecl): ClassDecl = {
        classDecl.methods.filter(m => m._2 match {
            case _: UpdateMethodDecl => true
            case _ => false
        }).foldLeft(classDecl)((c, m) => process(c, m._2.body)(m._2.operationLevel))
    }

    private def process(classDecl: ClassDecl, expr: IRExpr)(implicit methodOp: OperationLevel): ClassDecl = {
        expr match {
            case SetField(fieldId, _) =>
                val newFields = classDecl.fields.map {
                    case (id, decl) if id == fieldId =>
                        val newTyp = decl.typ match {
                            case CompoundType(b, c, m) => CompoundType(b, c lub methodOp.consistencyType(), m)
                            case _ => ???
                        }
                        id -> lang.FieldDecl(id, newTyp)
                    case x => x
                }
                classDecl.copy(fields = newFields)

            case CallUpdate(recvExpr, _, _) =>
                recvExpr match {
                    case GetField(fieldId) =>
                        val newFields = classDecl.fields.map {
                            case (id, decl) if id == fieldId =>
                                val newTyp = decl.typ match {
                                    case CompoundType(b, c, m) => CompoundType(b, c lub methodOp.consistencyType(), m)
                                    case _ => ???
                                }
                                id -> lang.FieldDecl(id, newTyp)
                            case x => x
                        }
                        classDecl.copy(fields = newFields)

                    case _ => classDecl
                }

            case Let(_, namedExpr, body) =>
                val r = process(classDecl, namedExpr)
                process(r, body)

            case If(conditionExpr, thenExpr, elseExpr) =>
                var r = process(classDecl, conditionExpr)
                r = process(r, thenExpr)
                process(r, elseExpr)

            case Equals(e1, e2) =>
                val r = process(classDecl, e1)
                process(r, e2)

            case Transaction(body) =>
                process(classDecl, body)

            case Sequence(exprs) =>
                exprs.foldLeft(classDecl)((r, expr) => process(r, expr))

            case _ => classDecl // TODO
        }
    }
}
