package de.tuda.stg.consys.invariants.lang

case class ClassTable(classes : ClassDef*) {

	private lazy val index : Map[ClassId, ClassDef] =
		classes.map(cls => (cls.name, cls)).toMap

	def getOrElse[B >: ClassDef](c : ClassId, orElse : => B) : B =
		index.getOrElse(c, orElse)

	def apply(c : ClassId) : ClassDef = index(c)

}
