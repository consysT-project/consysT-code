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
        val numberClass = ClassDecl(
            "BoxedNum",
            Seq(ConsistencyVarDecl("C", Inconsistent)),
            Seq.empty,
            SuperClassDecl(topClassId, Seq.empty, Seq.empty),
            Map(
                "v" -> FieldDecl(
                    "v",
                    Types.numberType(ConsistencyVar("C")),
                    Default(NumberTypeSuffix, Local, Immutable)
                )
            ),
            Map(
                "get" -> QueryMethodDecl("get", ConsistencyVar("C"),
                    Seq.empty,
                    Types.numberType(ConsistencyVar("C")),
                    Sequence(
                        Block(
                            Seq(
                                (Types.numberType(ConsistencyVar("C")),
                                    "x",
                                    Default(NumberTypeSuffix, ConsistencyVar("C"), Immutable))
                            ),
                            Sequence(
                                GetField("x", "v"),
                                ReturnExpr(Var("x"))
                            )
                        ),
                        Error
                    )
                ),
            )
        )

        val boxClass = ClassDecl(
            "Box",
            Seq(ConsistencyVarDecl("R", Weak), ConsistencyVarDecl("W", Weak)),
            Seq(TypeVarDecl("T", LocalTypeSuffix(topType), Mutable)),
            SuperClassDecl(topClassId, Seq.empty, Seq.empty),
            Map(
                "value" -> FieldDecl(
                    "value",
                    Type(ConsistencyVar("W"), Immutable, TypeSuffixVar("T")),
                    Default(TypeSuffixVar("T"), ConsistencyVar("W"), Immutable)),
            ),
            Map(
                "setVal" -> UpdateMethodDecl("setVal", ConsistencyVar("W"),
                    Seq(
                        VarDecl("x", Type(ConsistencyVar("W"), Immutable, TypeSuffixVar("T")))
                    ),
                    Sequence(SetField("value", Var("x")), ReturnExpr(UnitLiteral))
                ),
                "getVal" -> QueryMethodDecl("getVal", ConsistencyVar("W"),
                    Seq.empty,
                    Type(ConsistencyVar("W"), Immutable, TypeSuffixVar("T")),
                    Sequence(
                        Block(
                            Seq(
                                (Type(ConsistencyVar("W"), Immutable, TypeSuffixVar("T")),
                                    "x",
                                    Default(TypeSuffixVar("T"), ConsistencyVar("W"), Immutable))
                            ),
                            Sequence(GetField("x", "value"),
                                ReturnExpr(Var("x"))
                            )
                        ),
                        Error
                    )
                ),
                "peekVal" -> QueryMethodDecl("peekVal", ConsistencyVar("R"),
                    Seq.empty,
                    Type(ConsistencyUnion(ConsistencyVar("R"), ConsistencyVar("W")), Immutable, TypeSuffixVar("T")),
                    Sequence(
                        Block(
                            Seq(
                                (Type(ConsistencyUnion(ConsistencyVar("R"), ConsistencyVar("W")), Immutable, TypeSuffixVar("T")),
                                    "x",
                                    Default(TypeSuffixVar("T"), ConsistencyUnion(ConsistencyVar("R"), ConsistencyVar("W")), Immutable))
                            ),
                            Sequence(GetField("x", "value"),
                                ReturnExpr(Var("x"))
                            )
                        ),
                        Error
                    )
                ),
            )
        )

        ProgramDecl(
            Map(
                "BoxedNum" -> numberClass,
                "Box" -> boxClass
            ),
            Array(
                Transaction(
                    Block(
                        Seq(
                            (Types.refType(ClassType("Box", Seq(Weak, Strong), Seq(LocalTypeSuffix(ClassType("BoxedNum", Seq(Strong), Seq.empty))))),
                                "r",
                                Default(RefTypeSuffix(ClassType("Box", Seq(Weak, Strong), Seq(LocalTypeSuffix(ClassType("BoxedNum", Seq(Strong), Seq.empty))))), Local, Mutable)),
                            (Types.localType(Strong, ClassType("BoxedNum", Seq(Strong), Seq.empty)),
                                "x",
                                Default(LocalTypeSuffix(ClassType("BoxedNum", Seq(Local), Seq.empty)), Local, Immutable)),
                            (Types.localType(Weak, ClassType("BoxedNum", Seq(Strong), Seq.empty)),
                                "x2",
                                Default(LocalTypeSuffix(ClassType("BoxedNum", Seq(Local), Seq.empty)), Local, Immutable)),
                            (Types.numberType(Strong),
                                "n",
                                Default(NumberTypeSuffix, Local, Immutable)),
                            (Types.numberType(Weak),
                                "n2",
                                Default(NumberTypeSuffix, Local, Immutable))
                        ),
                        Sequence(
                            Replicate("r", "box1",
                                ClassType("Box", Seq(Weak, Strong), Seq(LocalTypeSuffix(ClassType("BoxedNum", Seq(Strong), Seq.empty)))),
                                Map("value" -> LocalObj(ClassType("BoxedNum", Seq(Local), Seq.empty), Map("v" -> Num(42))))),
                            Sequence(CallQuery("x", Var("r"), "getVal", Seq.empty),
                                Sequence(CallQuery("n", Var("x"), "get", Seq.empty),
                                    Sequence(Let("x", LocalObj(ClassType("BoxedNum", Seq(Strong), Seq.empty), Map("v" -> ArithmeticOperation(Var("n"), Num(1), Add)))),
                                        Sequence(CallUpdate(Var("r"), "setVal", Seq(Var("x"))),
                                            Sequence(CallQuery("x2", Var("r"), "peekVal", Seq.empty),
                                                Sequence(CallQuery("n2", Var("x2"), "get", Seq.empty),
                                                    Print(Var("n2"))
                                                )
                                            )
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
