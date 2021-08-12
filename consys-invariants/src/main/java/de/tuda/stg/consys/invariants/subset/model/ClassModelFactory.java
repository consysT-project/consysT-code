package de.tuda.stg.consys.invariants.subset.model;

import com.google.common.collect.Lists;
import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.ProgramModel;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.Arrays;
import java.util.List;
import java.util.function.BiConsumer;
import java.util.function.Consumer;

public class ClassModelFactory {

	private final ProgramModel model;

	public ClassModelFactory(ProgramModel model) {
		this.model = model;
	}

	public void generateModelForClasses(Iterable<JmlTypeDeclaration> jmlTypes, Consumer<BaseClassModel> doWithClassModel) {
		List<BaseClassModel> generatedModels = Lists.newLinkedList();

		for (var jmlType : jmlTypes) {
			if (jmlType.annotations != null) {
				var hasDataModelAnnotation = Arrays.stream(jmlType.annotations)
						.anyMatch(anno -> JDTUtils.typeIsTypeOfName(anno.resolvedType, "de.tuda.stg.consys.annotations.invariants.DataModel"));
				var hasReplicatedModelAnnotation = Arrays.stream(jmlType.annotations)
						.anyMatch(anno -> JDTUtils.typeIsTypeOfName(anno.resolvedType, "de.tuda.stg.consys.annotations.invariants.ReplicatedModel"));

				BaseClassModel classModel = null;

				if (hasDataModelAnnotation) {
					classModel = new BaseClassModel(model, jmlType, false);
				} else if (hasReplicatedModelAnnotation) {
					classModel = new ReplicatedClassModel(model, jmlType, false);
				}

				if (classModel != null) {
					generatedModels.add(classModel);
					continue;
				}
			}

			Logger.warn("class is not part of the constraints model: " + String.valueOf(jmlType.name));
		}

		for (BaseClassModel classModel : generatedModels) {
			classModel.initializeFields();
			classModel.initializeSort();
			doWithClassModel.accept(classModel);
		}

		for (BaseClassModel classModel : generatedModels) {
			classModel.initializeMethods();
			if (classModel instanceof ReplicatedClassModel) {
				((ReplicatedClassModel) classModel).initializeMergeMethod();
			}
		}
	}
}
