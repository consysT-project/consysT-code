package de.tuda.stg.consys.checker.qual;

import java.lang.annotation.*;

@Target({ElementType.TYPE})
@Retention(RetentionPolicy.RUNTIME)
public @interface OperationForConsistency {
    Class<? extends Annotation> value();
}
