package de.tuda.stg.consys.experimental.lang

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
}
