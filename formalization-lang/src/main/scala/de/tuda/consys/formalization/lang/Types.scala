package de.tuda.consys.formalization.lang

trait TypeLike[A] {
    def <=(t: A): Boolean

    def !<=(t: A): Boolean = !this.<=(t)

    def >=(t: A): Boolean

    def !>=(t: A): Boolean = !this.>=(t)

    def lub(t: A): A

    def glb(t: A): A
}

sealed trait Type {
    def <=(t: Type): Boolean

    def !<=(t: Type): Boolean = !this.<=(t)

    def >=(t: Type): Boolean

    def !>=(t: Type): Boolean = !this.>=(t)

    def lub(t: Type): Type

    def glb(t: Type): Type

    def effectiveType(): CompoundType
}

sealed trait ConsistencyType extends TypeLike[ConsistencyType] {
    def <=(t: ConsistencyType): Boolean = ConsistencyTypeLattice(this).hasUpperBound(t)

    def >=(t: ConsistencyType): Boolean = ConsistencyTypeLattice(this).hasLowerBound(t)

    def lub(t: ConsistencyType): ConsistencyType = {
        if (this <= t) t else this // TODO: generalize
    }

    def glb(t: ConsistencyType): ConsistencyType = {
        if (this >= t) t else this // TODO: generalize
    }

    def operationLevel(): OperationLevel
}

case object Local extends ConsistencyType {
    override def operationLevel(): OperationLevel = ???
}

case object Strong extends ConsistencyType {
    override def operationLevel(): OperationLevel = StrongOp
}

case object Mixed extends ConsistencyType {
    override def operationLevel(): OperationLevel = WeakOp
}

case object Weak extends ConsistencyType {
    override def operationLevel(): OperationLevel = WeakOp
}

case object Inconsistent extends ConsistencyType {
    override def operationLevel(): OperationLevel = ???
}

case object PolyConsistent extends ConsistencyType {
    override def operationLevel(): OperationLevel = ???
}

object ConsistencyTypeLattice {
    private lazy val local: LatticeNode[ConsistencyType] = new LatticeNode(Local, List(strong), List())
    private lazy val strong: LatticeNode[ConsistencyType] = new LatticeNode(Strong, List(mixed), List(local))
    private lazy val mixed: LatticeNode[ConsistencyType] = new LatticeNode(Mixed, List(weak), List(strong))
    private lazy val weak: LatticeNode[ConsistencyType] = new LatticeNode(Weak, List(inconsistent), List(mixed))
    private lazy val inconsistent: LatticeNode[ConsistencyType] = new LatticeNode(Weak, List(), List(weak))

    def apply(t: ConsistencyType): LatticeNode[ConsistencyType] = t match {
        case Local => local
        case Strong => strong
        case Mixed => mixed
        case Weak => weak
        case Inconsistent => inconsistent
    }
}

sealed trait MutabilityType extends TypeLike[MutabilityType] {
    def <=(t: MutabilityType): Boolean = MutabilityTypeLattice(this).hasUpperBound(t)

    def >=(t: MutabilityType): Boolean = MutabilityTypeLattice(this).hasLowerBound(t)

    def lub(t: MutabilityType): MutabilityType = ???

    def glb(t: MutabilityType): MutabilityType = ???
}

case object Mutable extends MutabilityType

case object Immutable extends MutabilityType

case object Bottom extends MutabilityType

object MutabilityTypeLattice {
    private lazy val bottom: LatticeNode[MutabilityType] = new LatticeNode(Bottom, List(mutable), Nil)
    private lazy val mutable: LatticeNode[MutabilityType] = new LatticeNode(Mutable, List(immutable), List(bottom))
    private lazy val immutable: LatticeNode[MutabilityType] = new LatticeNode(Immutable, Nil, List(mutable))

    def apply(t: MutabilityType): LatticeNode[MutabilityType] = t match {
        case Bottom => bottom
        case Mutable => mutable
        case Immutable => immutable
    }
}

case class ClassType(classId: ClassId, typeArguments: Seq[Type]) {
    override def toString: ClassId = if (typeArguments.isEmpty) s"$classId" else s"$classId<${typeArguments.mkString(",")}>"
}

case class CompoundType(classType: ClassType, consistencyType: ConsistencyType, mutabilityType: MutabilityType) extends Type {
    if (mutabilityType == Bottom && consistencyType != Local)
        sys.error("invalid bottom type")

    def <=(t: Type): Boolean = t match {
        case CompoundType(baseType1, consistencyType1, mutabilityType1) =>
            if (classType != baseType1)
                false // TODO: inheritance
            else if (consistencyType == Local && mutabilityType == Bottom) // TODO
                true
            else if (mutabilityType1 == Immutable)
                mutabilityType <= mutabilityType1 && consistencyType <= consistencyType1
            else
                mutabilityType <= mutabilityType1 && consistencyType == consistencyType1
        case _ => false
    }

    def >=(t: Type): Boolean = t match {
        case CompoundType(baseType, consistencyType, mutabilityType) => this == t || !(this <= t)
        case _ => false
    }

    def lub(t: Type): Type = t match {
        case CompoundType(baseType, consistencyType, mutabilityType) => ???
        case _ => ???
    }

    def glb(t: Type): Type = t match {
        case CompoundType(baseType, consistencyType, mutabilityType) => ???
        case _ => ???
    }

    def effectiveType(): CompoundType = this

    override def toString: ClassId = s"$mutabilityType $consistencyType $classType"
}

case class TypeVar(typeVarId: TypeVarId, upperBound: Type) extends Type {
    def <=(t: Type): Boolean = ???

    def >=(t: Type): Boolean = ???

    def lub(t: Type): Type = ???

    def glb(t: Type): Type = ???

    def effectiveType(): CompoundType = upperBound match {
        case t@CompoundType(_, _, _) => t
        case t@TypeVar(_, _) => t.effectiveType()
        case _ => ???
    }

    override def toString: ClassId = s"$typeVarId <: $upperBound"
}

trait OperationLevel {
    def consistencyType(): ConsistencyType
}

case object StrongOp extends OperationLevel {
    override def consistencyType(): ConsistencyType = Strong
}

case object WeakOp extends OperationLevel {
    override def consistencyType(): ConsistencyType = Weak
}



class LatticeNode[T](value: T, parents: => List[LatticeNode[T]], children: => List[LatticeNode[T]]) {
    def hasUpperBound(t: T): Boolean = t match {
        case `value` => true
        case _ => parents.exists(p => p.hasUpperBound(t))
    }

    def hasLowerBound(t: T): Boolean = t match {
        case `value` => true
        case _ => children.exists(p => p.hasLowerBound(t))
    }
}
