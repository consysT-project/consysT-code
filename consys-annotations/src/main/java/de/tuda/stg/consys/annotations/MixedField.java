package de.tuda.stg.consys.annotations;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Target({ElementType.FIELD})
@Retention(RetentionPolicy.RUNTIME)
public @interface MixedField {
    String consistencyForWeakDefault() default "";
    String consistencyForStrongDefault() default "";
}
