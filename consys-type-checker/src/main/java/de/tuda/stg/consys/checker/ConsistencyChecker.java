package de.tuda.stg.consys.checker;

import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.Tree;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.qual.StubFiles;
import org.checkerframework.framework.source.SupportedOptions;
import org.checkerframework.framework.source.SuppressWarningsPrefix;
import org.checkerframework.javacutil.BugInCF;
import scala.Tuple2;

import javax.lang.model.element.Element;
import java.util.*;

@StubFiles({"stubjdk.astub"})
@SupportedOptions({"projectPackage"})
@SuppressWarningsPrefix({"consistency"})
public class ConsistencyChecker extends BaseTypeChecker {
    private final Stack<Boolean> captureErrorsAndWarnings = new Stack<>();
    private final Stack<StringBuilder> capturedErrors = new Stack<>();
    private final Stack<StringBuilder> capturedWarnings = new Stack<>();

    public ConsistencyChecker(){
        super();
    }

    @Override
    protected BaseTypeVisitor<?> createSourceVisitor() {
        return new ConsistencyVisitor(this);
    }

    @Override
    public void reportError(Object source, @CompilerMessageKey String messageKey, Object... args) {
        // overwrite ref() access to be side-effect free
        if (messageKey.equals("purity.not.sideeffectfree.call") && source instanceof MethodInvocationTree &&
                TypeFactoryUtils.isAnyRefAccess((MethodInvocationTree) source, getTypeFactory())) {
            return;
        }

        if (captureErrorsAndWarnings.isEmpty() || !captureErrorsAndWarnings.peek()) {
            super.reportError(source, messageKey, args);
        } else if (!shouldSuppressWarnings(source, messageKey)) {
            capturedErrors.peek().append("\n - error:").append(formatCapturedError(source, messageKey, args));
        }
    }

    @Override
    public void reportWarning(Object source, @CompilerMessageKey String messageKey, Object... args) {
        if (captureErrorsAndWarnings.isEmpty() || !captureErrorsAndWarnings.peek()) {
            super.reportWarning(source, messageKey, args);
        } else if (!shouldSuppressWarnings(source, messageKey)) {
            capturedWarnings.peek().append("\n - warning:").append(formatCapturedError(source, messageKey, args));
        }
    }

    private boolean shouldSuppressWarnings(Object src, String errKey) {
        if (src instanceof Element) {
            return shouldSuppressWarnings((Element) src, errKey);
        } else if (src instanceof Tree) {
            return shouldSuppressWarnings((Tree) src, errKey);
        } else if (src == null) {
            return false;
        } else {
            throw new BugInCF("Unexpected source " + src);
        }
    }

    public void enableLogCapture() {
        captureErrorsAndWarnings.push(true);
        capturedErrors.push(new StringBuilder());
        capturedWarnings.push(new StringBuilder());
    }

    public Tuple2<String, String> disableLogCapture() {
        captureErrorsAndWarnings.pop();
        String errors = capturedErrors.pop().toString();
        String warnings = capturedWarnings.pop().toString();
        return new Tuple2<>(errors, warnings);
    }

    private String formatCapturedError(Object source, @CompilerMessageKey String messageKey, Object... args) {
        return "(" + messageKey + ")";
    }
}