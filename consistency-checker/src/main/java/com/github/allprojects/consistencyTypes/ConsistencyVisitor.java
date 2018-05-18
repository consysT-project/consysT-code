package com.github.allprojects.consistencyTypes;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;

public class ConsistencyVisitor extends BaseTypeVisitor<ConsistencyAnnotatedTypeFactory>{

    public ConsistencyVisitor(BaseTypeChecker checker) {
        super(checker);
    }



}
