package de.tudarmstadt.consistency.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Created on 28.08.18.
 *
 * @author Mirko Köhler
 */
@Target({ElementType.TYPE_PARAMETER, ElementType.TYPE, ElementType.PARAMETER})
@Retention(RetentionPolicy.RUNTIME)
public @interface CassandraType {
	String cassandraType();
}
