package de.tuda.stg.consys.checker.qual;

import java.lang.annotation.Annotation;

public @interface MixedField {
    String[] fields();
    // {field-fqn}:{annotation-fqn}[]
}
