package com.github.allprojects.consistencyTypes.qual;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import org.checkerframework.framework.qual.*;

@SubtypeOf({Low.class})
@ImplicitFor(
        literals = {LiteralKind.ALL}
)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@Retention(RetentionPolicy.RUNTIME)
@DefaultFor({TypeUseLocation.LOWER_BOUND})

public @interface High {}
