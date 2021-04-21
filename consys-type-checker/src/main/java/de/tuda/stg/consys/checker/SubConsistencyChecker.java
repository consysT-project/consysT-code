package de.tuda.stg.consys.checker;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.source.DiagMessage;
import org.checkerframework.framework.source.SuppressWarningsPrefix;

import javax.tools.Diagnostic;

@SuppressWarningsPrefix({"consistency"})
public class SubConsistencyChecker extends BaseTypeChecker {
    private boolean internalReporting;
    private boolean failure;
    private Object src;

    @Override
    public void reportError(Object src, String messageKey, Object... args) {
        if (internalReporting) {
            failure = (messageKey.contains("implicitflow") || messageKey.contains("type.incompatible"));
            this.src = src;
        } else {
            super.reportError(src, messageKey, args);
        }
    }

    public void enableInternalReporting() {
        internalReporting = true;
    }

    public void disableInternalReporting() {
        failure = false;
        internalReporting = false;
    }

    public boolean hasFailureOccurred(){
        return failure;
    }

    public Object getSrc() {
        return src;
    }

    public String getQualifier() {
        return null;
    }

    public static class StrongSubConsistencyChecker extends SubConsistencyChecker {
        @Override
        protected BaseTypeVisitor<?> createSourceVisitor() {
            return new SubConsistencyVisitor(this);
        }

        @Override
        public String getQualifier() {
            return "de.tuda.stg.consys.checker.qual.Strong";
        }
    }

    public static class WeakSubConsistencyChecker extends SubConsistencyChecker {
        @Override
        protected BaseTypeVisitor<?> createSourceVisitor() {
            return new SubConsistencyVisitor(this);
        }

        @Override
        public String getQualifier() {
            return "de.tuda.stg.consys.checker.qual.Weak";
        }
    }
}
