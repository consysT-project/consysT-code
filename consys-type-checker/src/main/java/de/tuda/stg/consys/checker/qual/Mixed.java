package de.tuda.stg.consys.checker.qual;

import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.*;

@SubtypeOf({Inconsistent.class})
@Target({ElementType.TYPE_USE})
@Retention(RetentionPolicy.RUNTIME)
public @interface Mixed {
    Class<? extends Annotation> withDefault() default WeakOp.class;
}