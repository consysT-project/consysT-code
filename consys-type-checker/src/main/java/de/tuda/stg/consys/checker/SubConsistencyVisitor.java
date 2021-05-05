package de.tuda.stg.consys.checker;

import com.sun.source.tree.ClassTree;

import javax.lang.model.type.DeclaredType;


public class SubConsistencyVisitor extends ConsistencyVisitorImpl {
    public SubConsistencyVisitor(SubConsistencyChecker checker) {
        super(checker);
    }

    @Override
    protected ConsistencyAnnotatedTypeFactory createTypeFactory() {
        return new SubConsistencyAnnotatedTypeFactory((SubConsistencyChecker) checker);
    }

    @Override
    public void processClassTree(ClassTree classTree) {
        SubConsistencyChecker classChecker = (SubConsistencyChecker) checker;

        classChecker.enableInternalReporting();

        super.processClassTree(classTree);
        if (classChecker.hasFailureOccurred()) {
            DeclaredType classType = atypeFactory.getAnnotatedType(classTree).getUnderlyingType();
            ((SubConsistencyAnnotatedTypeFactory) atypeFactory).addDisallowedReplication(classType, classChecker.getSrc());
        }

        classChecker.disableInternalReporting();
        System.out.println("-----------------------------");
    }
}
