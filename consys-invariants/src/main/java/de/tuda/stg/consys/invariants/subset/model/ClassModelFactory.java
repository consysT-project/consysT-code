package de.tuda.stg.consys.invariants.subset.model;

import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.util.Arrays;
import java.util.Optional;

public class ClassModelFactory {

	private final ProgramModel model;

	public ClassModelFactory(ProgramModel model) {
		this.model = model;
	}

	public Optional<BaseClassModel> generateModelFor(JmlTypeDeclaration jmlType) {
		if (jmlType.annotations != null) {

			var hasDataModelAnnotation = Arrays.stream(jmlType.annotations)
					.anyMatch(anno -> JDTUtils.typeIsTypeOfName(anno.resolvedType, "de.tuda.stg.consys.annotations.invariants.DataModel"));
			var hasReplicatedModelAnnotation = Arrays.stream(jmlType.annotations)
					.anyMatch(anno -> JDTUtils.typeIsTypeOfName(anno.resolvedType, "de.tuda.stg.consys.annotations.invariants.ReplicatedModel"));

			if (hasDataModelAnnotation) {
				return Optional.of(new BaseClassModel(model, jmlType));
			} else if (hasReplicatedModelAnnotation) {
				return Optional.of(new ReplicatedClassModel(model, jmlType));
			}
		}

		Logger.warn("class is not part of the constraints model: " + String.valueOf(jmlType.name));
		return Optional.empty();

	}
}
