package de.tuda.stg.consys.checker;

import java.lang.annotation.*;

@Target({ElementType.TYPE})
@Retention(RetentionPolicy.RUNTIME)
public @interface QualifierForOperation {
    Class<? extends Annotation> value();
}
