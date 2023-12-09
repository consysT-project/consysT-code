package de.tuda.consys.formalization.examples

import de.tuda.consys.formalization.lang._
import de.tuda.consys.formalization.lang.types._
import de.tuda.consys.formalization.{CassandraInitializer, Interpreter, TypeChecker}

import scala.concurrent.{Await, ExecutionContext, ExecutionContextExecutor, Future}
import scala.concurrent.duration._

object Shop {
    def main(args : Array[String]): Unit = {
        TypeChecker.checkProgram(program)

        CassandraInitializer.initialize("127.0.0.1")

        implicit val ec: ExecutionContextExecutor = ExecutionContext.global
        val f0 = Future{
            new Interpreter("127.0.0.1").run(program.classTable, program.processes(0))
            println("Task 0 done")
        }
        Await.result(f0, 1.minutes)

        val f1 = Future{
            new Interpreter("127.0.0.2").run(program.classTable, program.processes(1))
            println("Task 1 done")
        }
        val f2 = Future{
            new Interpreter("127.0.0.3").run(program.classTable, program.processes(2))
            println("Task 2 done")
        }

        Await.result(f1, 1.minutes)
        Await.result(f2, 1.minutes)
    }

    private val userClassName = "User"
    private val userClassType = ClassType(userClassName, Seq.empty, Seq.empty)
    private val userClass = ClassDecl(
        userClassName,
        Seq.empty,
        Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map(
            "id" -> FieldDecl("id", Types.numberType(Local), Num(-1)),
            "balance" -> FieldDecl("balance", Types.numberType(Strong), Num(0)),
        ),
        Map(
            "withdraw" -> UpdateMethodDecl(
                "withdraw",
                Strong,
                Seq(VarDecl("x", Types.numberType(Strong))),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Strong), "temp", Num(0))),
                        Statements.sequence(Seq(
                            GetField("temp", "balance"),
                            Let("temp", ArithmeticOperation(Var("temp"), Var("x"), Subtract)),
                            SetField("balance", Var("temp")),
                        ))
                    ),
                    ReturnExpr(UnitLiteral)
                ))
            ),
            "deposit" -> UpdateMethodDecl(
                "deposit",
                Strong,
                Seq(VarDecl("x", Types.numberType(Strong))),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Strong), "temp", Num(0))),
                        Statements.sequence(Seq(
                            GetField("temp", "balance"),
                            Let("temp", ArithmeticOperation(Var("temp"), Var("x"), Add)),
                            SetField("balance", Var("temp")),
                        ))
                    ),
                    ReturnExpr(UnitLiteral)
                ))
            ),
            "getId" -> QueryMethodDecl(
                "getId",
                Local,
                Seq.empty,
                Types.numberType(Local),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Local), "temp", Num(-1))),
                        Statements.sequence(Seq(
                            GetField("temp", "id"),
                            ReturnExpr(Var("temp"))
                        ))
                    ),
                    ReturnExpr(Num(-1))
                ))
            ),
            "getBalance" -> QueryMethodDecl(
                "getBalance",
                Strong,
                Seq.empty,
                Types.numberType(Strong),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Strong), "temp", Num(-1))),
                        Statements.sequence(Seq(
                            GetField("temp", "balance"),
                            ReturnExpr(Var("temp"))
                        ))
                    ),
                    ReturnExpr(Num(-1))
                ))
            ),
            "peekBalance" -> QueryMethodDecl(
                "peekBalance",
                Weak,
                Seq.empty,
                Types.numberType(Weak),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Weak), "temp", Num(-1))),
                        Statements.sequence(Seq(
                            GetField("temp", "balance"),
                            ReturnExpr(Var("temp"))
                        ))
                    ),
                    ReturnExpr(Num(-1))
                ))
            )
        )
    )

    private val itemClassName = "Item"
    private val itemClassType = ClassType(itemClassName, Seq.empty, Seq.empty)
    private val itemClass = ClassDecl(
        itemClassName,
        Seq.empty,
        Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map(
            "id" -> FieldDecl("id", Types.numberType(Local), Num(-1)),
            "cost" -> FieldDecl("cost", Types.numberType(Strong), Num(0)),
            "inventory" -> FieldDecl("inventory", Types.numberType(Strong), Num(0)),
            "description" -> FieldDecl("description", Types.stringType(Weak), StringLiteral(""))
        ),
        Map(
            "sellOne" -> UpdateMethodDecl(
                "sellOne",
                Strong,
                Seq.empty,
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Strong), "temp", Num(0))),
                        Statements.sequence(Seq(
                            GetField("temp", "inventory"),
                            Let("temp", ArithmeticOperation(Var("temp"), Num(1), Subtract)),
                            SetField("inventory", Var("temp")),
                        ))
                    ),
                    ReturnExpr(UnitLiteral)
                ))
            ),
            "addInventory" -> UpdateMethodDecl(
                "addInventory",
                Strong,
                Seq(VarDecl("x", Types.numberType(Strong))),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Strong), "temp", Num(0))),
                        Statements.sequence(Seq(
                            GetField("temp", "inventory"),
                            Let("temp", ArithmeticOperation(Var("temp"), Var("x"), Add)),
                            SetField("inventory", Var("temp")),
                        ))
                    ),
                    ReturnExpr(UnitLiteral)
                ))
            ),
            "setCost" -> UpdateMethodDecl(
                "setCost",
                Strong,
                Seq(VarDecl("x", Types.numberType(Strong))),
                Statements.sequence(Seq(
                    SetField("cost", Var("x")),
                    ReturnExpr(UnitLiteral)
                ))
            ),
            "setDescription" -> UpdateMethodDecl(
                "setDescription",
                Weak,
                Seq(VarDecl("x", Types.stringType(Weak))),
                Statements.sequence(Seq(
                    SetField("description", Var("x")),
                    ReturnExpr(UnitLiteral)
                ))
            ),
            "getId" -> QueryMethodDecl(
                "getId",
                Local,
                Seq.empty,
                Types.numberType(Local),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Local), "temp", Num(-1))),
                        Statements.sequence(Seq(
                            GetField("temp", "id"),
                            ReturnExpr(Var("temp"))
                        ))
                    ),
                    ReturnExpr(Num(-1))
                ))
            ),
            "getInventory" -> QueryMethodDecl(
                "getInventory",
                Strong,
                Seq.empty,
                Types.numberType(Strong),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Strong), "temp", Num(-1))),
                        Statements.sequence(Seq(
                            GetField("temp", "inventory"),
                            ReturnExpr(Var("temp"))
                        ))
                    ),
                    ReturnExpr(Num(-1))
                ))
            ),
            "getCost" -> QueryMethodDecl(
                "getCost",
                Strong,
                Seq.empty,
                Types.numberType(Strong),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Strong), "temp", Num(-1))),
                        Statements.sequence(Seq(
                            GetField("temp", "cost"),
                            ReturnExpr(Var("temp"))
                        ))
                    ),
                    ReturnExpr(Num(-1))
                ))
            ),
            "peekCost" -> QueryMethodDecl(
                "peekCost",
                Weak,
                Seq.empty,
                Types.numberType(Weak),
                Statements.sequence(Seq(
                    Block(Seq((Types.numberType(Weak), "temp", Num(-1))),
                        Statements.sequence(Seq(
                            GetField("temp", "cost"),
                            ReturnExpr(Var("temp"))
                        ))
                    ),
                    ReturnExpr(Num(-1))
                ))
            ),
            "getDescription" -> QueryMethodDecl(
                "getDescription",
                Weak,
                Seq.empty,
                Types.stringType(Weak),
                Statements.sequence(Seq(
                    Block(Seq((Types.stringType(Weak), "temp", Num(-1))),
                        Statements.sequence(Seq(
                            GetField("temp", "description"),
                            ReturnExpr(Var("temp"))
                        ))
                    ),
                    ReturnExpr(StringLiteral(""))
                ))
            ),
        )
    )

    private val shopClassName = "Shop"
    private val shopClassType = ClassType(shopClassName, Seq.empty, Seq.empty)
    private val shopClass = ClassDecl(
        shopClassName,
        Seq.empty,
        Seq.empty,
        SuperClassDecl(topClassId, Seq.empty, Seq.empty),
        Map(
            "id" -> FieldDecl("id", Types.numberType(Local), Num(-1)),
        ),
        Map(
            "buy" -> UpdateMethodDecl(
                "buy",
                Strong,
                Seq(
                    VarDecl("user", Types.refType(Strong, Mutable, userClassType)),
                    VarDecl("item", Types.refType(Strong, Mutable, itemClassType))
                ),
                Statements.sequence(Seq(
                    Block(
                        Seq(
                            (Types.numberType(Strong), "balance", Num(0)),
                            (Types.numberType(Strong), "cost", Num(0)),
                            (Types.numberType(Strong), "inventory", Num(0))
                        ),
                        Statements.sequence(Seq(
                            CallQuery("balance", Var("user"), "getBalance", Seq.empty),
                            CallQuery("cost", Var("item"), "getCost", Seq.empty),
                            CallQuery("inventory", Var("item"), "getInventory", Seq.empty),
                            If(
                                BooleanCombination(
                                    ArithmeticComparison(Var("inventory"), Num(0), GreaterThan),
                                    ArithmeticComparison(Var("balance"), Var("cost"), GreaterOrEqualThan),
                                    And),
                                Statements.sequence(Seq(
                                    CallUpdate(Var("user"), "withdraw", Seq(Var("cost"))),
                                    CallUpdate(Var("item"), "sellOne", Seq.empty),
                                )),
                                Skip
                            )
                        ))
                    ),
                    ReturnExpr(UnitLiteral)
                ))
            )
        )
    )

    private val classTable = Map(
        userClassName -> userClass,
        itemClassName -> itemClass,
        shopClassName -> shopClass,
    )

    private val process0 = Block(
        Seq(
            (Types.refType(Local, Mutable, shopClassType), "shop", Default(RefTypeSuffix(shopClassType), Mutable)),
            (Types.refType(Local, Mutable, userClassType), "user", Default(RefTypeSuffix(userClassType), Mutable)),
            (Types.refType(Local, Mutable, itemClassType), "item", Default(RefTypeSuffix(itemClassType), Mutable)),
        ),
        Statements.sequence(Seq(
            Print(StringLiteral("Start of process 0")),
            Transaction(
                Statements.sequence(Seq(
                    Replicate("shop", "shop-1", shopClassType, Map(
                        "id" -> Num(0),
                    )),
                    Replicate("item", "item-1", itemClassType, Map(
                        "id" -> Num(1),
                        "cost" -> Num(5),
                        "description" -> StringLiteral("A great book!"),
                        "inventory" -> Num(10),
                    )),
                    Replicate("user", "user-1", userClassType, Map(
                        "id" -> Num(1),
                        "balance" -> Num(100),
                    )),
                    Replicate("user", "user-2", userClassType, Map(
                        "id" -> Num(2),
                        "balance" -> Num(100),
                    )),
                )),
                Print(StringLiteral("Error"))
            ),
            Print(StringLiteral("End of process 0")),
        ))
    )

    private val process1 = Block(
        Seq(
            (Types.refType(Local, Mutable, shopClassType), "shop", Ref("shop-1", shopClassType)),
            (Types.refType(Local, Mutable, userClassType), "user", Ref("user-1", userClassType)),
            (Types.refType(Local, Mutable, itemClassType), "item", Ref("item-1", itemClassType)),
            (Types.numberType, "i", Num(0)),
            (Types.numberType(Inconsistent), "temp", Num(-1)),
        ),
        Statements.sequence(Seq(
            Print(StringLiteral("Start of process 1")),
            Transaction(
                Statements.sequence(Seq(
                    While(
                        ArithmeticComparison(Var("i"), Num(3), LessThan),
                        Statements.sequence(Seq(
                            CallUpdate(Var("shop"), "buy", Seq(Var("user"), Var("item"))),
                            Let("i", ArithmeticOperation(Var("i"), Num(1), Add)),
                        )),
                    ),
                    CallUpdate(Var("item"), "setDescription", Seq(StringLiteral("A great book! Second edition."))),
                    CallQuery("temp", Var("user"), "getBalance", Seq.empty),
                    Print(StringLiteral("Balance of user 1:")),
                    Print(Var("temp")),
                    CallQuery("temp", Var("item"), "getInventory", Seq.empty),
                    Print(StringLiteral("Inventory of item:")),
                    Print(Var("temp")),
                )),
                Print(StringLiteral("Error"))
            ),
            Let("i", Num(0)),
            Print(StringLiteral("End of transaction")),
            Transaction(
                Statements.sequence(Seq(
                    While(
                        ArithmeticComparison(Var("i"), Num(7), LessThan),
                        Statements.sequence(Seq(
                            CallUpdate(Var("shop"), "buy", Seq(Var("user"), Var("item"))),
                            Let("i", ArithmeticOperation(Var("i"), Num(1), Add)),
                        )),
                    ),
                    CallQuery("temp", Var("user"), "getBalance", Seq.empty),
                    Print(StringLiteral("Balance of user 1:")),
                    Print(Var("temp")),
                    CallQuery("temp", Var("item"), "getInventory", Seq.empty),
                    Print(StringLiteral("Inventory of item:")),
                    Print(Var("temp")),
                )),
                Print(StringLiteral("Error"))
            ),
            Print(StringLiteral("End of process 1")),
        ))
    )

    private val process2 = Block(
        Seq(
            (Types.refType(Local, Mutable, shopClassType), "shop", Ref("shop-1", shopClassType)),
            (Types.refType(Local, Mutable, userClassType), "user", Ref("user-2", userClassType)),
            (Types.refType(Local, Mutable, itemClassType), "item", Ref("item-1", itemClassType)),
            (Types.numberType, "i", Num(0)),
            (Types.numberType(Inconsistent), "temp", Num(-1)),
        ),
        Statements.sequence(Seq(
            Print(StringLiteral("Start of process 2")),
            Transaction(
                Statements.sequence(Seq(
                    While(
                        ArithmeticComparison(Var("i"), Num(3), LessThan),
                        Statements.sequence(Seq(
                            CallUpdate(Var("shop"), "buy", Seq(Var("user"), Var("item"))),
                            Let("i", ArithmeticOperation(Var("i"), Num(1), Add)),
                        )),
                    ),
                    CallQuery("temp", Var("user"), "getBalance", Seq.empty),
                    Print(StringLiteral("Balance of user 2:")),
                    Print(Var("temp")),
                    CallQuery("temp", Var("item"), "getInventory", Seq.empty),
                    Print(StringLiteral("Inventory of item:")),
                    Print(Var("temp")),
                )),
                Print(StringLiteral("Error"))
            ),
            Print(StringLiteral("End of process 2")),
        ))
    )

    private val program = ProgramDecl(classTable, Array(process0, process1, process2))
}
