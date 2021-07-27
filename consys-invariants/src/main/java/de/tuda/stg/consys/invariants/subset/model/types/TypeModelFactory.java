package de.tuda.stg.consys.invariants.subset.model.types;

import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.utils.Lazy;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.lookup.*;

import javax.xml.transform.Source;
import java.util.Arrays;
import java.util.Optional;

public class TypeModelFactory {

	private final ProgramModel model;

	private final Lazy<IntModel> intModel;
	private final Lazy<BoolModel> boolModel;
	private final Lazy<RealModel> realModel;
	private final Lazy<VoidModel> emptyModel;
	private final Lazy<RefModel> refModel;
	private final Lazy<StringModel> stringModel;



	public TypeModelFactory(ProgramModel model) {
		this.model = model;
		this.intModel = Lazy.make(() -> new IntModel(model));
		this.boolModel = Lazy.make(() -> new BoolModel(model));
		this.realModel = Lazy.make(() -> new RealModel(model));
		this.emptyModel = Lazy.make(() -> new VoidModel(model));
		this.refModel = Lazy.make(() -> new RefModel(model, "T_Ref"));
		this.stringModel = Lazy.make(() -> new StringModel(model));
	}

	public TypeModel<?> typeFor(TypeBinding typeBinding) {
		if (typeBinding instanceof BaseTypeBinding) {
			BaseTypeBinding binding = (BaseTypeBinding) typeBinding;

			switch (binding.id) {
				case 2: // char
				case 3: // byte
				case 4: // short
				case 7: // long
				case 10: // int
					return intModel.get();
				case 8: // double
				case 9: // float
					return realModel.get();
				case 5: // boolean
					return boolModel.get();
				case 6: // void
					return emptyModel.get();
				default:
					//throw new IllegalArgumentException("incompatible base type " + typeBinding);
					return new EmptyModel(model, "incompatible base type " + typeBinding);
			}
		} else if (typeBinding instanceof ArrayBinding) {
			ArrayBinding arrayBinding = (ArrayBinding) typeBinding;
			// translate element type
			TypeModel elementType = typeFor(arrayBinding.leafComponentType);


			if (elementType.hasSort()) {
				// build array sort from index and element type
				return new ArrayModel(model, elementType);//
			} else {
				return new EmptyModel(model, "incompatible array element type in " + typeBinding);
			}

		} else if (typeBinding instanceof ReferenceBinding) {
			ReferenceBinding refBinding = (ReferenceBinding) typeBinding;

			if (bindingIsType(refBinding, "java.lang.String")) {
				return stringModel.get();
			} else if (typeBinding instanceof MissingTypeBinding) {
				System.err.println("missing type binding: " + typeBinding);
				throw new IllegalArgumentException("unsupported type binding: " + typeBinding);
			}

			return refModel.get();
		} else {
			return new EmptyModel(model, "incompatible type " + typeBinding);
		}
	}

	public TypeModel<?> typeFor(TypeReference typeReference) {
		return typeFor(typeReference.resolvedType);
	}

	/**
	 *
	 * @param binding
	 * @param typeName A name of the form "java.lang.Object"
	 * @return
	 */
	private boolean bindingIsType(ReferenceBinding binding, String typeName) {
		return typeName.equals(String.valueOf(binding.readableName()/* ~ "java.lang.Object" */));
	}
}
