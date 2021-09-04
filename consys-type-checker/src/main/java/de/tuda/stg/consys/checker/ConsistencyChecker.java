package de.tuda.stg.consys.checker;

import com.sun.source.tree.MethodInvocationTree;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SupportedLintOptions;
import org.checkerframework.framework.source.SuppressWarningsPrefix;
import scala.Tuple3;

import java.util.*;

@SuppressWarningsPrefix({"consistency"})
public class ConsistencyChecker extends BaseTypeChecker {

    public List<Tuple3<Object, String, List<Object>>> errors = new LinkedList<>();
    public List<Tuple3<Object, String, List<Object>>> warnings = new LinkedList<>();
    public boolean printErrors = true;

    public ConsistencyChecker(){
        super();
    }

    @Override
    public void reportError(Object source, @CompilerMessageKey String messageKey, Object... args) {
        // overwrite ref() access to be side-effect free
        if (messageKey.equals("purity.not.sideeffectfree.call") && source instanceof MethodInvocationTree &&
                ((ConsistencyVisitorImpl)getVisitor()).methodInvocationIsRefAccess((MethodInvocationTree) source)) {
            return;
        }
        // TODO: remove this hack for ref type arguments
        if (messageKey.equals("type.argument.type.incompatible")) {
            return;
        }

        if (printErrors) {
            super.reportError(source, messageKey, args);
        } else {
            errors.add(new Tuple3<>(source, messageKey, Arrays.asList(args)));
        }
    }

    @Override
    public void reportWarning(Object source, @CompilerMessageKey String messageKey, Object... args) {
        if (printErrors) {
            super.reportWarning(source, messageKey, args);
        } else {
            warnings.add(new Tuple3<>(source, messageKey, Arrays.asList(args)));
        }
    }
}