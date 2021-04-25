package de.tuda.stg.consys.checker.qual;

import java.lang.annotation.*;

@Target({ElementType.METHOD})
@Retention(RetentionPolicy.RUNTIME)
@OperationForConsistency(Weak.class)
public @interface WeakOp {
}
