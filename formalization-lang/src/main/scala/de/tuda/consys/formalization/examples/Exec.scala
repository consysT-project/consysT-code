package de.tuda.consys.formalization.examples

import de.tuda.consys.formalization.{Interpreter, TypeChecker}
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.types._

object Exec {
    def main(args : Array[String]): Unit = {
        val program = exampleProgram1()
        TypeChecker.checkProgram(program)
        new Interpreter("127.0.0.1").run(program)
    }

    private def exampleProgram1(): ProgramDecl = {
        val boxClass = ClassDecl(
            "Box",
            Seq.empty,
            Seq.empty,
            SuperClassDecl("Object", Seq.empty, Seq.empty),
            Map(
                "value" -> FieldDecl("value", Type(Strong, Mutable, LocalTypeSuffix(Natives.numberType))),
            ),
            Map(
                "setVal" -> UpdateMethodDecl("setVal", Strong,
                    Seq(
                        VarDecl("x", Type(Strong, Mutable, LocalTypeSuffix(Natives.numberType)))
                    ),
                    Sequence(SetField("value", Var("x")), Return)
                ),
                "getVal" -> QueryMethodDecl("getVal", Strong, Seq.empty, Type(Strong, Mutable, LocalTypeSuffix(Natives.numberType)),
                    Sequence(GetField("x", "value"), ReturnExpr(Var("x")))
                ),
            )
        )

        ProgramDecl(
            Map(
                "Number" -> Natives.numberClass,
                "Bool" -> Natives.booleanClass,
                "Unit" -> Natives.unitClass,
                "Box" -> boxClass,
            ),
            Transaction(
                Sequence(Replicate("x", "box1", ClassType("Box", Seq.empty, Seq.empty), Seq(Num(42)), Strong, Mutable),
                    Sequence(CallQuery("r", Var("x"), "getVal", Seq.empty),
                        Sequence(Let("n", Add(Var("r"), Num(1))),
                            Sequence(CallUpdate(Var("x"), "setVal", Seq(Var("n"))),
                                Sequence(CallQuery("r", Var("x"), "getVal", Seq.empty),
                                    Print(Var("r"))
                                )
                            )
                        )
                    )
                ),
                Skip
            )
        )
    }
}
