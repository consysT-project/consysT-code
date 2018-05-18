package de.tu_darmstadt.consistency_types.checker;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SuppressWarningsKeys;

@SuppressWarningsKeys({"consistency"})
public class ConsistencyChecker extends  BaseTypeChecker {
    public ConsistencyChecker(){
        System.out.println("Running consisteny checker...");
    }
}