package de.tuda.consys.formalization.lang

import de.tuda.consys.formalization.lang.types.{ClassType, ConsistencyType, MutabilityType, Type}

sealed trait Statement

case object Skip extends Statement

case object Error extends Statement

case class ReturnExpr(e: Expression) extends Statement

case class Block(vars: Seq[(Type, VarId, Expression)],
                 s: Statement
                ) extends Statement

case class Sequence(s1: Statement,
                    s2: Statement
                   ) extends Statement

case class If(conditionExpr: Expression,
              thenStmt: Statement,
              elseStmt: Statement
             ) extends Statement

case class While(condition: Expression,
                 stmt: Statement
                ) extends Statement

case class Let(varId: VarId,
               e: Expression
              ) extends Statement

case class SetField(fieldId: FieldId,
                    valueExpr: Expression
                   ) extends Statement

case class GetField(varId: VarId,
                    fieldId: FieldId
                   ) extends Statement

case class CallUpdate(recvExpr: Expression,
                      methodId: MethodId,
                      argumentExprs: Seq[Expression]
                     ) extends Statement

case class CallUpdateThis(methodId: MethodId,
                          argumentExprs: Seq[Expression]
                         ) extends Statement

case class EvalUpdate(recv: Expression,
                      methodId: MethodId,
                      args: Map[VarId, Expression],
                      body: Statement
                     ) extends Statement

case class CallQuery(varId: VarId,
                     recvExpr: Expression,
                     methodId: MethodId,
                     argumentExprs: Seq[Expression]
                    ) extends Statement

case class CallQueryThis(varId: VarId,
                         methodId: MethodId,
                         argumentExprs: Seq[Expression]
                        ) extends Statement

case class EvalQuery(varId: VarId,
                     recv: Expression,
                     methodId: MethodId,
                     args: Map[VarId, Expression],
                     body: Statement
                    )  extends Statement

case class Replicate(varId: VarId,
                     refId: String,
                     classType: ClassType,
                     constructor: Map[FieldId, Expression]
                    ) extends Statement

case class Transaction(body: Statement,
                       except: Statement
                      ) extends Statement

case class Print(expression: Expression) extends Statement

object Statements {
  def sequence(stmts: Seq[Statement]): Statement =
    stmts.foldLeft[Statement](Skip)((s1, s2) => Sequence(s1, s2))
}
