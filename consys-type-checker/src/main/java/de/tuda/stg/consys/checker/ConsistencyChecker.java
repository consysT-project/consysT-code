package de.tuda.stg.consys.checker;

import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
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
        var checkers = super.getImmediateSubcheckerClasses();
        //checkers.add(SubConsistencyChecker.WeakSubConsistencyChecker.class);
        //checkers.add(SubConsistencyChecker.StrongSubConsistencyChecker.class);
        return checkers;
    }

    @Override
    public void reportError(Object source, @CompilerMessageKey String messageKey, Object... args) {
        super.reportError(source, messageKey, args);
    }

    @Override
    public void reportWarning(Object source, @CompilerMessageKey String messageKey, Object... args) {
        super.reportWarning(source, messageKey, args);
    }
}