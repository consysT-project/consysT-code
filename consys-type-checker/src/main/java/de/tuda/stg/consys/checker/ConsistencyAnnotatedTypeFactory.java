package de.tuda.stg.consys.checker;

import de.tuda.stg.consys.checker.qual.Inconsistent;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.qual.TypeUseLocation;
import org.checkerframework.framework.type.DefaultTypeHierarchy;
import org.checkerframework.framework.type.TypeHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.ListTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.framework.util.defaults.QualifierDefaults;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;

public class ConsistencyAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {

	protected final AnnotationMirror STRONG_CONSISTENCY =
			AnnotationBuilder.fromClass(elements, Strong.class);

	protected final AnnotationMirror WEAK_CONSISTENCY =
			AnnotationBuilder.fromClass(elements, Weak.class);

	protected final AnnotationMirror INCONSISTENT_CONSISTENCY =
			AnnotationBuilder.fromClass(elements, Inconsistent.class);

	protected final AnnotationMirror LOCAL_CONSISTENCY =
			AnnotationBuilder.fromClass(elements, Local.class);

	public ConsistencyAnnotatedTypeFactory(BaseTypeChecker checker) {
        /*
        	Set useFlow to false if the flow analysis should be used.
         */
		super(checker, false);
		if (this.getClass().equals(ConsistencyAnnotatedTypeFactory.class)) {
			this.postInit();
		}
	}


	@Override
	protected TreeAnnotator createTreeAnnotator() {
		TreeAnnotator others = super.createTreeAnnotator();
		return new ListTreeAnnotator(others, new ConsistencyTreeAnnotator(this));
	}

	@Override
	protected TypeAnnotator createTypeAnnotator() {
		TypeAnnotator others = super.createTypeAnnotator();
		return new ListTypeAnnotator(others, new ConsistencyTypeAnnotator(this));
	}

	@Override
	protected TypeHierarchy createTypeHierarchy() {

		DefaultTypeHierarchy hierarchy = new DefaultTypeHierarchy(
			checker, getQualifierHierarchy(), checker.getBooleanOption("ignoreRawTypeArguments", true), checker.hasOption("invariantArrays"));

		return new ConsistencyTypeHierarchy(hierarchy, this);
	}

	@Override
	protected void addCheckedCodeDefaults(QualifierDefaults defs) {

		// TODO: Check
		defs.addCheckedCodeDefault(INCONSISTENT_CONSISTENCY, TypeUseLocation.FIELD);


		super.addCheckedCodeDefaults(defs);
	}

	protected void addCheckedCodeDefaultsSkip(QualifierDefaults defs) {
		super.addCheckedCodeDefaults(defs);
	}


//    @Override
//    //Trees: check bodies of methods
//    protected void addComputedTypeAnnotations(Tree tree, AnnotatedTypeMirror type, boolean iUseFlow) {
//        super.addComputedTypeAnnotations(tree, type, iUseFlow);
//    }
//
//    @Override
//    //Elements: packages, classes, or methods
//    public void addComputedTypeAnnotations(Element elt, AnnotatedTypeMirror type) {
//        super.addComputedTypeAnnotations(elt, type);
//    }

}
