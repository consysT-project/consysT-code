package de.tuda.stg.consys.experimental.lang

/**
 * Created on 29.11.19.
 *
 * @author Mirko Köhler
 */
private[lang] case class OObject[FieldId, Value, MethodId, MethodDef](fields : Map[FieldId, Value], methods : Map[MethodId, MethodDef])

