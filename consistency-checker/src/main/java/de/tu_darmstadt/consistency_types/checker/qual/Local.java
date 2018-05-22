package de.tu_darmstadt.consistency_types.checker.qual;

import org.checkerframework.framework.qual.*;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@SubtypeOf({Strong.class})
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@Retention(RetentionPolicy.RUNTIME)
@DefaultFor({TypeUseLocation.LOWER_BOUND})
@ImplicitFor(
        literals = {LiteralKind.ALL}
)
public @interface Local {}
