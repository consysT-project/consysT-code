package com.github.allprojects.consistencyTypes;

import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;

public class ConsistencyAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {
    public ConsistencyAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker, false);
        this.postInit();
    }
}
