package de.tuda.consys.formalization.examples

import de.tuda.consys.formalization.{Interpreter, Preprocessor, TypeChecker}
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.types._

object Exec {
    def main(args : Array[String]): Unit = {
        var program = exampleProgram2()
        program = Preprocessor.process(program)
        TypeChecker.checkProgram(program)
        val result = new Interpreter("127.0.0.1").run(program)
        println(s"Done with result: $result")
    }

    private def exampleProgram1(): ProgramDecl = {
        val boxClass = ClassDecl(
            "Box",
            Seq(),
            ("Object", Seq.empty),
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
                //("Box", Mixed) -> boxClass,
                //("Box", Weak) -> boxClass,
                ("Box", Strong) -> boxClass,
            ),
            Transaction(
                Let("x", New("b", "Box", Seq(), Strong, Map("value" -> Num(42))),
                    Let("n", Add(CallQuery(Var("x"), "getVal", Seq()), Num(1)),
                        Sequence(Seq(
                            CallUpdate(Var("x"), "setVal", Seq(Var("n"))),
                            CallQuery(Var("x"), "getVal", Seq())
                        ))
                    )
                )
            )
        )
    }

    private def exampleProgram2(): ProgramDecl = {
        val polyBoxClass = ClassDecl(
            "Box",
            Seq(TypeVarDecl("T", CompoundType(Natives.objectType, Inconsistent, Immutable))),
            ("Object", Seq.empty),
            Map(
                "value" -> FieldDecl("value", TypeVar("T")),
            ),
            Map(
                "setVal" -> UpdateMethodDecl("setVal", StrongOp,
                    Seq(
                        VarDecl("x", TypeVar("T"))
                    ),
                    Sequence(
                        Seq(SetField("value", Var("x")),
                            UnitLiteral
                        ))
                ),
                "getVal" -> QueryMethodDecl("getVal", StrongOp, Seq(), TypeVar("T"),
                    GetField("value")
                ),
            )
        )

        ProgramDecl(
            Map(
                ("Object", Weak) -> Natives.objectClass,
                ("Object", Strong) -> Natives.objectClass,
                ("Number", Weak) -> Natives.numberClass,
                ("Number", Strong) -> Natives.numberClass,
                ("Bool", Weak) -> Natives.booleanClass,
                ("Bool", Strong) -> Natives.booleanClass,
                ("Unit", Weak) -> Natives.unitClass,
                ("Unit", Strong) -> Natives.unitClass,
                //("Box", Mixed) -> boxCls,
                //("Box", Weak) -> boxCls,
                ("Box", Strong) -> polyBoxClass,
            ),
            Transaction(
                Let("x", New("b", "Box", Seq(CompoundType(Natives.numberType, Strong, Mutable)), Strong, Map("value" -> Num(42))),
                    Let("n", Add(CallQuery(Var("x"), "getVal", Seq()), Num(1)),
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
