package de.tuda.stg.consys.checker;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Created on 28.05.19.
 *
 * @author Mirko Köhler
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.FIELD})
//UNUSED AT THE MOMENT
public @interface Inferred {
}
