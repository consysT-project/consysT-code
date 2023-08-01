package lang

case object NumberType extends ClassType("Number", Seq.empty)

val numberClass = ClassDecl("Number", Seq.empty, Map.empty, Map.empty)

case object BooleanType extends ClassType("Boolean", Seq.empty)

val booleanClass = ClassDecl("Boolean", Seq.empty, Map.empty, Map.empty)

case object UnitType extends ClassType("Unit", Seq.empty)

val unitClass = ClassDecl("Unit", Seq.empty, Map.empty, Map.empty)
