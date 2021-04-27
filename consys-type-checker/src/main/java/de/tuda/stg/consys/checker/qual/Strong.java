package de.tuda.stg.consys.checker.qual;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@SubtypeOf({Weak.class})
@Target({ElementType.TYPE_USE})
@Retention(RetentionPolicy.RUNTIME)
@QualifierForOperation(StrongOp.class)
public @interface Strong {}
