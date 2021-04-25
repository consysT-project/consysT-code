package de.tuda.stg.consys.checker.qual;

import org.checkerframework.framework.qual.*;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Bottom type of the consistency type lattice.
 *
 * All literal values are local, and thus can be assigned to weak or strong distributed types.
 *
 * The name is used for local *values*, local variables are by default inconsistent (everything can be assigned to them).
 */
@SubtypeOf({Strong.class, Mixed.class})
@Target({ElementType.TYPE_USE})
@Retention(RetentionPolicy.RUNTIME)
@QualifierForLiterals
@DefaultFor(value = {TypeUseLocation.LOWER_BOUND}, types = {Object.class})
public @interface Local {}
