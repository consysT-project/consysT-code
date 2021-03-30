package de.tuda.stg.consys.checker;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SuppressWarningsKeys;

import java.util.LinkedHashSet;

@SuppressWarningsKeys({"consistency"})
public class ConsistencyChecker extends BaseTypeChecker {

    public ConsistencyChecker(){
        super();
    }

    @Override
    protected LinkedHashSet<Class<? extends BaseTypeChecker>> getImmediateSubcheckerClasses() {
        LinkedHashSet<Class<? extends BaseTypeChecker>> checkers = super.getImmediateSubcheckerClasses();
        checkers.add(SubConsistencyChecker.WeakSubConsistencyChecker.class);
        checkers.add(SubConsistencyChecker.StrongSubConsistencyChecker.class);
        return checkers;
    }
}