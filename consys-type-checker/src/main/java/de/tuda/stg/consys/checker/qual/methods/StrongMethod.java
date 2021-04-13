package de.tuda.stg.consys.checker.qual.methods;

import de.tuda.stg.consys.checker.qual.Weak;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@SubtypeOf({WeakMethod.class})
@Target({ElementType.METHOD})
@Retention(RetentionPolicy.RUNTIME)
public @interface StrongMethod {}
