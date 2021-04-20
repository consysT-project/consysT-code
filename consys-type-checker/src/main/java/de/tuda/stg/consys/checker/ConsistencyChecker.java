package de.tuda.stg.consys.checker;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SupportedLintOptions;
import org.checkerframework.framework.source.SuppressWarningsPrefix;

import java.util.LinkedHashSet;

@SupportedLintOptions({"disableSubChecker"})
@SuppressWarningsPrefix({"consistency"})
public class ConsistencyChecker extends BaseTypeChecker {

    public ConsistencyChecker(){
        super();
    }

    @Override
    protected LinkedHashSet<Class<? extends BaseTypeChecker>> getImmediateSubcheckerClasses() {
        //if (getLintOption("disableSubChecker", false))
        //    return new LinkedHashSet<>();

        //LinkedHashSet<Class<? extends BaseTypeChecker>> checkers = super.getImmediateSubcheckerClasses();
        //checkers.add(SubConsistencyChecker.WeakSubConsistencyChecker.class);
        //checkers.add(SubConsistencyChecker.StrongSubConsistencyChecker.class);
        //return checkers;
        return super.getImmediateSubcheckerClasses();
    }
}