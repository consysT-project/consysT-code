package de.tuda.stg.consys.checker.qual;

import org.checkerframework.framework.qual.DefaultFor;
import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;
import org.checkerframework.framework.qual.TypeUseLocation;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@SubtypeOf({})
@Target({ElementType.TYPE_USE})
@Retention(RetentionPolicy.RUNTIME)
@DefaultQualifierInHierarchy
@DefaultFor({TypeUseLocation.LOCAL_VARIABLE, TypeUseLocation.FIELD})
public @interface Inconsistent {}