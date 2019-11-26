package de.tuda.stg.consys.checker;

import org.checkerframework.common.basetype.BaseAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.type.DefaultTypeHierarchy;
import org.checkerframework.framework.type.TypeHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.ListTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;

public class ConsistencyAnnotatedTypeFactory extends BaseAnnotatedTypeFactory {


	public ConsistencyAnnotatedTypeFactory(BaseTypeChecker checker) {
        /*
        	Set useFlow to false if the flow analysis should be used.
         */
		super(checker, true);
		this.postInit();
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
