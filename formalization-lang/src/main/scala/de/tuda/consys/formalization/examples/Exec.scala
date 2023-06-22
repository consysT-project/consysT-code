package de.tuda.consys.formalization.examples

import de.tuda.consys.formalization.{Interpreter, Preprocessor, TypeChecker}
import de.tuda.consys.formalization.lang._

object Exec {
    def main(args : Array[String]): Unit = {
        var program = exampleProgram1()
        program = Preprocessor.process(program)
        TypeChecker.checkProgram(program)
        val result = new Interpreter("127.0.0.1").run(program)
        println(s"Done with result: $result")
    }

    private def exampleProgram1(): ProgramDecl = {
        val boxCls = ClassDecl(
            "Box",
            Seq(),
            Map(
                "value" -> FieldDecl("value", CompoundType(Natives.numberType, Strong, Mutable)),
            ),
            Map(
                "setVal" -> UpdateMethodDecl("setVal", StrongOp,
                    Seq(
                        VarDecl("x", CompoundType(Natives.numberType, Strong, Mutable))
                    ),
                    Sequence(
                        Seq(SetField("value", Var("x")),
                            UnitLiteral
                        ))
                ),
                "getVal" -> QueryMethodDecl("getVal", StrongOp, Seq(), CompoundType(Natives.numberType, Strong, Mutable),
                    GetField("value")
                ),
            )
        )

        ProgramDecl(
            Map(
                ("Number", Weak) -> Natives.numberClass,
                ("Number", Strong) -> Natives.numberClass,
                ("Bool", Weak) -> Natives.booleanClass,
                ("Bool", Strong) -> Natives.booleanClass,
                ("Unit", Weak) -> Natives.unitClass,
                ("Unit", Strong) -> Natives.unitClass,
                //("Box", Mixed) -> boxCls,
                //("Box", Weak) -> boxCls,
                ("Box", Strong) -> boxCls,
            ),
            Transaction(
                Let("x", New("b", "Box", Seq(), Strong, Map("value" -> Num(1))),
                    Let("n", Num(42),
                        Sequence(Seq(
                            CallUpdate(Var("x"), "setVal", Seq(Var("n"))),
                            CallQuery(Var("x"), "getVal", Seq())
                        ))
                    )
                )
            )
        )
    }
}
