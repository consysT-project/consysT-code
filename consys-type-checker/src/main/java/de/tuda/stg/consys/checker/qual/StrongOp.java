package de.tuda.stg.consys.checker.qual;

import java.lang.annotation.*;

@Target({ElementType.METHOD})
@Retention(RetentionPolicy.RUNTIME)
@OperationForConsistency(Strong.class)
public @interface StrongOp{
}
