package de.tu_darmstadt.consistency_types.checker;

import com.sun.source.tree.Tree;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.ErrorReporter;
import org.checkerframework.javacutil.TreeUtils;

public class ConsistencyAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {
    public ConsistencyAnnotatedTypeFactory(BaseTypeChecker checker) {
        /*
        	Set useFlow to false if the flow analysis should be used.
         */
        super(checker, false);
        this.postInit();
    }


}
