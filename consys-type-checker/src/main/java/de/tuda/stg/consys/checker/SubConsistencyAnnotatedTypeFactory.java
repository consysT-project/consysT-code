package de.tuda.stg.consys.checker;

import org.checkerframework.framework.qual.TypeUseLocation;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationBuilder;

import javax.lang.model.type.DeclaredType;
import java.util.HashMap;
import java.util.Map;


public class SubConsistencyAnnotatedTypeFactory extends ConsistencyAnnotatedTypeFactory {
    Map<DeclaredType, Object> disallowedReplications;

    SubConsistencyAnnotatedTypeFactory(SubConsistencyChecker checker) {
        super(checker);

        this.disallowedReplications = new HashMap<>();

        this.postInit();
    }

    @Override
    protected void addCheckedCodeDefaults(QualifierDefaults defs) {
        defs.addCheckedCodeDefault(
                AnnotationBuilder.fromClass(getElementUtils(), ((SubConsistencyChecker) checker).getQualifier()),
                TypeUseLocation.FIELD);

        super.addCheckedCodeDefaultsSkip(defs);
    }

    public void addDisallowedReplication(DeclaredType classType, Object src) {
        disallowedReplications.put(classType, src);
    }

    public boolean isAllowed(DeclaredType classType) {
        return !disallowedReplications.containsKey(classType);
    }

    public Object getSrcForDisallowed(DeclaredType classType) {
        return disallowedReplications.get(classType);
    }
}
