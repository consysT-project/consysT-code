package de.tuda.stg.consys.experimental.lang

import de.tuda.stg.consys.experimental.lang.ObjectStore.MapStore

/**
 * Created on 28.11.19.
 *
 * @author Mirko Köhler
 */
object LangBinding extends Syntax with LocalSemantics
	with OOSyntax with OOSemantics
	with IntSyntax with IntSemantics
{
	type VarId = Symbol
	type FieldId = String
	type MethodId = String
	type Location = Int

	override type ObjectStore = MapStore[Location, Obj]

	override protected def createReduction : LangBinding.Reduction =
		new Reduction with IntReduction with OOReduction {
			override protected val objStore : ObjectStore.MapStore[Int, LangBinding.Obj] = new MapStore[Location, Obj]
		}

	override protected def thisVar : Symbol = 'this
}
