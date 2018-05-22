package de.tu_darmstadt.consistency_types.checker;

import org.checkerframework.checker.tainting.TaintingChecker;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SuppressWarningsKeys;

@SuppressWarningsKeys({"consistency"})
public class ConsistencyChecker extends TaintingChecker {

    public ConsistencyChecker(){
        super();
        System.out.println("Running consistency checker...");
    }
}