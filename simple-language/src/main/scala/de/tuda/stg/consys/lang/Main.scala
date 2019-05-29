package de.tuda.stg.consys.lang

/**
	* Created on 29.05.19.
	*
	* @author Mirko Köhler
	*/
object Main extends App {

	object LangImpl extends Lang
	import LangImpl._

	val ct : ClassTable = Map(
		'Obj -> ClassDef('Obj, None, Seq(), Seq()),
		'Box -> ClassDef('Box, Some('Obj), Seq(InferredFieldDef('Obj, 'val)), Seq()),
		'Num -> ClassDef('Num, Some('Obj), Seq(), Seq()),
		'Zero -> ClassDef('Zero, Some('Num), Seq(), Seq()),
		'Succ -> ClassDef('Succ, Some('Num), Seq(InferredFieldDef('Num, 'pred)), Seq())
	)

	val env : TypeEnv = Map(
		'obj1 -> Type('Box, Strong),
		'x -> Type('Num, Weak)
	)

	val expr1 =
		New(Type('Box, Strong), 'obj1, Seq(New(Type('Zero, Weak), 'x, Seq())))




	val program = Program(ct, env, Seq(expr1))

	assert(progType(program))


}
