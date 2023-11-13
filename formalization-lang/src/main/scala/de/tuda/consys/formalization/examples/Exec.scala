package de.tuda.consys.formalization.examples

import de.tuda.consys.formalization.lang.Natives.topType
import de.tuda.consys.formalization.{Interpreter, TypeChecker}
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.types._

object Exec {
    def main(args : Array[String]): Unit = {
        val program = exampleProgram1()
        TypeChecker.checkProgram(program)
        new Interpreter("127.0.0.1").run(program.classTable, program.processes(0))
    }

    private def exampleProgram1(): ProgramDecl = {
        val boxClass = ClassDecl(
            "Box",
            Seq(ConsistencyVarDecl("R", Weak), ConsistencyVarDecl("W", Weak)),
            Seq(TypeVarDecl("T", LocalTypeSuffix(topType), Mutable)),
            SuperClassDecl(topClassId, Seq.empty, Seq.empty),
            Map(
                "value" -> FieldDecl("value", Type(ConsistencyVar("W"), Immutable, TypeSuffixVar("T"))),
            ),
            Map(
                "setVal" -> UpdateMethodDecl("setVal", Strong,
                    Seq(
                        VarDecl("x", Type(ConsistencyVar("W"), Immutable, TypeSuffixVar("T")))
                    ),
                    Type(Local, Immutable, LocalTypeSuffix(Natives.unitType)),
                    Sequence(SetField("value", Var("x")), ReturnExpr(UnitLiteral))
                ),
                "getVal" -> QueryMethodDecl("getVal", ConsistencyVar("R"),
                    Seq.empty,
                    Type(ConsistencyVar("R"), Immutable, TypeSuffixVar("T")),
                    Sequence(
                        Block(
                            Seq(
                                (Type(ConsistencyVar("R"), Immutable, TypeSuffixVar("T")), "x", Num(0))
                            ),
                            Sequence(GetField("x", "value"),
                                ReturnExpr(Var("x"))
                            )
                        ),
                        ReturnExpr(Num(Int.MaxValue))
                    )
                ),
            )
        )

        ProgramDecl(
            Map(
                "Box" -> boxClass,
            ) ++ Natives.initialClassTable,
            Array(
                Transaction(
                    Block(
                        Seq(
                            (Type(Local, Mutable, RefTypeSuffix(ClassType("Box", Seq.empty, Seq.empty))), "x", Ref("box1", ClassType("Box", Seq.empty, Seq.empty), Local, Mutable)),
                            (Type(Strong, Immutable, LocalTypeSuffix(Natives.numberType)), "n", Num(0)),
                            (Type(Local, Immutable, LocalTypeSuffix(Natives.topType)), "_", UnitLiteral)
                        ),
                        Sequence(Replicate("x", "box1", ClassType("Box", Seq.empty, Seq.empty), Map("value" -> Num(42)), Local, Mutable),
                            Sequence(CallQuery("n", Var("x"), "getVal", Seq.empty),
                                Sequence(Let("n", ArithmeticOperation(Var("n"), Num(1), Add)),
                                    Sequence(CallUpdate("_", Var("x"), "setVal", Seq(Var("n"))),
                                        Sequence(CallQuery("n", Var("x"), "getVal", Seq.empty),
                                            Print(Var("n"))
                                        )
                                    )
                                )
                            )
                        )
                    ),
                    Skip
                )
            )
        )
    }
}
