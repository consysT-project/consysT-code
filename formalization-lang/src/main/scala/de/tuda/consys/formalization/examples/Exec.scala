package de.tuda.consys.formalization.examples

import de.tuda.consys.formalization.lang.Natives.topType
import de.tuda.consys.formalization.{Interpreter, TypeChecker}
import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.types._

object Exec {
    def main(args : Array[String]): Unit = {
        val program = caseStudy()
        TypeChecker.checkProgram(program)
        new Interpreter("127.0.0.1").run(program.classTable, program.processes(0))
    }

    private def test(): Unit = {
        val c1 = ClassDecl(
            "C1",
            Seq.empty,
            Seq.empty,
            SuperClassDecl(topClassId, Seq.empty, Seq.empty),
            Map.empty,
            Map.empty
        )
        val c2 = ClassDecl(
            "C2",
            Seq.empty,
            Seq.empty,
            SuperClassDecl(c1.classId, Seq.empty, Seq.empty),
            Map.empty,
            Map.empty
        )
        val c3 = ClassDecl(
            "C3",
            Seq.empty,
            Seq.empty,
            SuperClassDecl(c2.classId, Seq.empty, Seq.empty),
            Map.empty,
            Map.empty
        )
        val ct = Map(
            "C1" -> c1,
            "C2" -> c2,
            "C3" -> c3
        )
        println(Subtyping.subtype(Mutable, c1.toType, c2.toType)(ct, Map.empty, Map.empty, Map.empty))
        println(Subtyping.subtype(Mutable, c2.toType, c1.toType)(ct, Map.empty, Map.empty, Map.empty))
        println(Subtyping.subtype(Mutable, c3.toType, c1.toType)(ct, Map.empty, Map.empty, Map.empty))

        val consEnv = Map("V1" -> Inconsistent)
        val v1 = ConsistencyVar("V1")
        println(Subtyping.subtype(Weak, ConsistencyUnion(Weak, Strong))(consEnv))
        println(Subtyping.subtype(v1, ConsistencyUnion(v1, Strong))(consEnv))
        println(Subtyping.subtype(v1, ConsistencyUnion(ConsistencyUnion(v1, Strong), Strong))(consEnv))
        println(Subtyping.subtype(ConsistencyUnion(v1, Strong), v1)(consEnv))
        println(Subtyping.subtype(ConsistencyUnion(v1, ConsistencyUnion(v1, Local)), v1)(consEnv))
    }

    private val numberClass = ClassDecl(
        "BoxedNum",
        Seq(ConsistencyVarDecl("C", Inconsistent)),
        Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map(
            "v" -> FieldDecl(
                "v",
                Types.numberType(ConsistencyVar("C")),
                Default(NumberTypeSuffix, Immutable)
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
                                Default(NumberTypeSuffix, Immutable))
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

    private def exampleProgram1(): ProgramDecl = {
        val boxClass = ClassDecl(
            "Box",
            Seq(ConsistencyVarDecl("R", Weak), ConsistencyVarDecl("W", Weak)),
            Seq(TypeVarDecl("T", LocalTypeSuffix(topType), Mutable)),
            SuperClassDecl(topClassId, Seq.empty, Seq.empty),
            Map(
                "value" -> FieldDecl(
                    "value",
                    Type(ConsistencyVar("W"), Immutable, TypeSuffixVar("T")),
                    Default(TypeSuffixVar("T"), Immutable)),
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
                                    Default(TypeSuffixVar("T"), Immutable))
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
                                    Default(TypeSuffixVar("T"), Immutable))
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
                                Default(RefTypeSuffix(ClassType("Box", Seq(Weak, Strong), Seq(LocalTypeSuffix(ClassType("BoxedNum", Seq(Strong), Seq.empty))))), Mutable)),
                            (Types.localType(Strong, ClassType("BoxedNum", Seq(Strong), Seq.empty)),
                                "x",
                                Default(LocalTypeSuffix(ClassType("BoxedNum", Seq(Local), Seq.empty)), Immutable)),
                            (Types.localType(Weak, ClassType("BoxedNum", Seq(Strong), Seq.empty)),
                                "x2",
                                Default(LocalTypeSuffix(ClassType("BoxedNum", Seq(Local), Seq.empty)), Immutable)),
                            (Types.numberType(Strong),
                                "n",
                                Default(NumberTypeSuffix, Immutable)),
                            (Types.numberType(Weak),
                                "n2",
                                Default(NumberTypeSuffix, Immutable)),
                            (Types.unitType(Inconsistent),
                                "_",
                                UnitLiteral)
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

    private def caseStudy(): ProgramDecl = {
        // TODO: must implement this list by references to get mutable operations on the values
        val listClass = ClassDecl(
            "List",
            Seq(ConsistencyVarDecl("R", Weak), ConsistencyVarDecl("W", Weak)),
            Seq(TypeVarDecl("T", RefTypeSuffix(topType), Mutable)),
            SuperClassDecl(topClassId, Seq.empty, Seq.empty),
            Map.empty,
            Map(
                "getTail" -> QueryMethodDecl(
                    "getTail",
                    ConsistencyVar("W"),
                    Seq.empty,
                    Type(ConsistencyVar("W"), Immutable, LocalTypeSuffix(
                        ClassType("List",
                            Seq(ConsistencyVar("R"), ConsistencyVar("W")),
                            Seq(TypeSuffixVar("T"))))),
                    Error
                ),
                "getValue" -> QueryMethodDecl(
                    "getValue",
                    ConsistencyVar("W"),
                    Seq.empty,
                    Type(ConsistencyVar("W"), Mutable, TypeSuffixVar("T")),
                    Error
                ),
                "peekValue" -> QueryMethodDecl(
                    "peekValue",
                    ConsistencyVar("R"),
                    Seq.empty,
                    Type(ConsistencyUnion(ConsistencyVar("R"), ConsistencyVar("W")), Immutable, TypeSuffixVar("T")),
                    Error
                ),
                "printValue" -> QueryMethodDecl(
                    "printValue",
                    ConsistencyVar("R"),
                    Seq.empty,
                    Types.unitType,
                    Error
                ),
            )
        )
        val consClass = ClassDecl(
            "Cons",
            Seq(ConsistencyVarDecl("R", Weak), ConsistencyVarDecl("W", Weak)),
            Seq(TypeVarDecl("T", RefTypeSuffix(topType), Mutable)),
            SuperClassDecl("List", Seq(ConsistencyVar("R"), ConsistencyVar("W")), Seq(TypeSuffixVar("T"))),
            Map(
                "value" -> FieldDecl(
                    "value",
                    Type(ConsistencyVar("W"), Mutable, TypeSuffixVar("T")),
                    Default(TypeSuffixVar("T"), Mutable)
                ),
                "tail" -> FieldDecl(
                    "tail",
                    Type(ConsistencyVar("W"), Mutable, RefTypeSuffix(
                        ClassType("List",
                            Seq(ConsistencyVar("R"), ConsistencyVar("W")),
                            Seq(TypeSuffixVar("T"))))),
                    Default(RefTypeSuffix(
                        ClassType("List",
                            Seq(ConsistencyVar("R"), ConsistencyVar("W")),
                            Seq(TypeSuffixVar("T")))), Mutable)
                )
            ),
            Map(
                "getTail" -> QueryMethodDecl("getTail", ConsistencyVar("W"),
                    Seq.empty,
                    Type(ConsistencyVar("W"), Mutable, RefTypeSuffix(
                        ClassType("List",
                            Seq(ConsistencyVar("R"), ConsistencyVar("W")),
                            Seq(TypeSuffixVar("T"))))),
                    Sequence(
                        Block(
                            Seq(
                                (Type(ConsistencyVar("W"), Mutable, RefTypeSuffix(
                                    ClassType("List",
                                        Seq(ConsistencyVar("R"), ConsistencyVar("W")),
                                        Seq(TypeSuffixVar("T"))))),
                                    "x",
                                    Default(RefTypeSuffix(
                                        ClassType("List",
                                            Seq(ConsistencyVar("R"), ConsistencyVar("W")),
                                            Seq(TypeSuffixVar("T")))),
                                        Immutable))
                            ),
                            Sequence(GetField("x", "tail"),
                                ReturnExpr(Var("x"))
                            )
                        ),
                        Error
                    )
                ),
                "getValue" -> QueryMethodDecl("getValue", ConsistencyVar("W"),
                    Seq.empty,
                    Type(ConsistencyVar("W"), Immutable, TypeSuffixVar("T")),
                    Sequence(
                        Block(
                            Seq(
                                (Type(ConsistencyVar("W"), Mutable, TypeSuffixVar("T")),
                                    "x",
                                    Default(TypeSuffixVar("T"), Mutable))
                            ),
                            Sequence(GetField("x", "value"),
                                ReturnExpr(Var("x"))
                            )
                        ),
                        Error
                    )
                ),
                "peekValue" -> QueryMethodDecl("peekValue", ConsistencyVar("R"),
                    Seq.empty,
                    Type(ConsistencyUnion(ConsistencyVar("R"), ConsistencyVar("W")), Immutable, TypeSuffixVar("T")),
                    Sequence(
                        Block(
                            Seq(
                                (Type(ConsistencyUnion(ConsistencyVar("R"), ConsistencyVar("W")), Immutable, TypeSuffixVar("T")),
                                    "x",
                                    Default(TypeSuffixVar("T"), Mutable))
                            ),
                            Sequence(GetField("x", "value"),
                                ReturnExpr(Var("x"))
                            )
                        ),
                        Error
                    )
                ),
                "printValue" -> QueryMethodDecl(
                    "printValue",
                    ConsistencyVar("R"),
                    Seq.empty,
                    Types.unitType,
                    Error
                ),
            )
        )
        val emptyListClass = ClassDecl(
            "Nil",
            Seq(ConsistencyVarDecl("R", Weak), ConsistencyVarDecl("W", Weak)),
            Seq(TypeVarDecl("T", RefTypeSuffix(topType), Mutable)),
            SuperClassDecl("List", Seq(ConsistencyVar("R"), ConsistencyVar("W")), Seq(TypeSuffixVar("T"))),
            Map.empty,
            Map.empty
        )

        val dummyClass = ClassDecl(
            "Dummy",
            Seq.empty,
            Seq.empty,
            SuperClassDecl(topClassId, Seq.empty, Seq.empty),
            Map.empty,
            Map.empty
        )

        ProgramDecl(
            Map(
                "BoxedNum" -> numberClass,
                "List" -> listClass,
                "Cons" -> consClass,
                "Nil" -> emptyListClass,
                "Dummy" -> dummyClass
            ),
            Array(
                Transaction(
                    Block(
                        Seq(
                            (
                                Types.localType(ClassType("List", Seq(Weak, Strong), Seq(RefTypeSuffix(ClassType("Dummy", Seq.empty, Seq.empty))))),
                                "l",
                                Default(LocalTypeSuffix(ClassType("List", Seq(Weak, Strong), Seq(LocalTypeSuffix(ClassType("Dummy", Seq.empty, Seq.empty))))), Immutable)
                            ),
                            (
                                Types.refType(ClassType("Dummy", Seq.empty, Seq.empty)),
                                "x",
                                Default(RefTypeSuffix(ClassType("Dummy", Seq.empty, Seq.empty)), Immutable)
                            )
                        ),
                        Statements.sequence(Seq(
                            Let("l",
                                LocalObj(
                                    ClassType("Cons", Seq(Weak, Strong), Seq(RefTypeSuffix(ClassType("Dummy", Seq.empty, Seq.empty)))),
                                    Map(
                                        "value" -> Ref("1", ClassType("Dummy", Seq.empty, Seq.empty)),
                                        "tail" -> LocalObj(
                                            ClassType("Cons", Seq(Weak, Strong), Seq(RefTypeSuffix(ClassType("Dummy", Seq.empty, Seq.empty)))),
                                            Map(
                                                "value" -> Ref("2", ClassType("Dummy", Seq.empty, Seq.empty)),
                                                "tail" -> LocalObj(ClassType("Nil", Seq(Weak, Strong), Seq(RefTypeSuffix(ClassType("Dummy", Seq.empty, Seq.empty)))), Map.empty)
                                            )
                                        )
                                    )
                                )
                            ),
                            CallQuery("x", Var("l"), "getValue", Seq.empty),
                            Print(Var("x"))
                        ))
                    ),
                    Error
                )
            )
        )
    }
}
