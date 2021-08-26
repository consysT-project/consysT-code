package de.tuda.stg.consys.invariants.subset.model.types;

import com.google.common.collect.Maps;
import de.tuda.stg.consys.invariants.subset.Logger;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import de.tuda.stg.consys.invariants.subset.utils.JDTUtils;
import de.tuda.stg.consys.invariants.subset.utils.Lazy;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.lookup.*;

import java.util.HashMap;

public class TypeModelFactory {

	private final ProgramModel model;

	private final Lazy<IntModel> intModel;
	private final Lazy<BoolModel> boolModel;
	private final Lazy<RealModel> realModel;
	private final Lazy<VoidModel> voidModel;
	private final Lazy<StringModel> stringModel;

	private final HashMap<ReferenceBinding, ObjectModel> refModels;

	public TypeModelFactory(ProgramModel model) {
		this.model = model;
		this.intModel = Lazy.make(() -> new IntModel(model));
		this.boolModel = Lazy.make(() -> new BoolModel(model));
		this.realModel = Lazy.make(() -> new RealModel(model));
		this.voidModel = Lazy.make(() -> new VoidModel(model));
		this.refModels = Maps.newHashMap();
		this.stringModel = Lazy.make(() -> new StringModel(model));
	}

	private ObjectModel modelForRef(ReferenceBinding refBinding) {
		var erased = JDTUtils.erase(refBinding);

		if (refModels.containsKey(erased)) {
			return refModels.get(erased);
		} else {
			var refModel = new ObjectModel(model, erased);
			refModels.put(erased, refModel);
			return refModel;
		}
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
					return voidModel.get();
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
		} else if (typeBinding instanceof TypeVariableBinding) {
			return typeFor(((TypeVariableBinding) typeBinding).superclass);
		} else if (typeBinding instanceof WildcardBinding) {
			return typeFor(((WildcardBinding) typeBinding).typeVariable().superclass);
		} else if (typeBinding instanceof ReferenceBinding) {
			ReferenceBinding refBinding = (ReferenceBinding) typeBinding;

			// Lookup if class is in the data model
			var mbClassModel = model.getClassModel(refBinding);
			if (mbClassModel.isPresent()) {
				return modelForRef(refBinding);
			}

			//... else handle some special cases
			if (JDTUtils.typeIsSubtypeOfName(refBinding, "java.lang.String")) {
				return stringModel.get();
			} else if (JDTUtils.typeIsSubtypeOfName(refBinding, "java.util.Set")) {
				if (refBinding instanceof ParameterizedTypeBinding) {
					ParameterizedTypeBinding parBinding = (ParameterizedTypeBinding) refBinding;
					return new SetModel(model, typeFor(parBinding.arguments[0]));
				} else {
					var objectModel = modelForRef(model.bindingForJavaLangObject());
					return new SetModel(model, objectModel);
				}
			} else if (JDTUtils.typeIsSubtypeOfName(refBinding, "com.google.common.collect.Multimap")) {
				if (refBinding instanceof ParameterizedTypeBinding) {
					ParameterizedTypeBinding parBinding = (ParameterizedTypeBinding) refBinding;
					return new MultimapModel(model, typeFor(parBinding.arguments[0]), typeFor(parBinding.arguments[1]));
				} else {
					var objectModel = modelForRef(model.bindingForJavaLangObject());
					return new MultimapModel(model, objectModel, objectModel);
				}
			} else if (JDTUtils.typeIsSubtypeOfName(refBinding, "java.util.Map")) {
				// Map<String, BigInteger>
				if (refBinding instanceof ParameterizedTypeBinding) {
					//Map has type parameters -> use them
					ParameterizedTypeBinding parBinding = (ParameterizedTypeBinding) refBinding;
					return new MapModel(model, typeFor(parBinding.arguments[0]), typeFor(parBinding.arguments[1]));
				} else {
					//not type parameters -> Map<Object, Object>
					var objectModel = modelForRef(model.bindingForJavaLangObject());
					return new MapModel(model, objectModel, objectModel);
				}
			}
			/* generic collections */
			else if (JDTUtils.typeIsSubtypeOfName(refBinding, "java.util.Collection")) {
				if (refBinding instanceof ParameterizedTypeBinding) {
					ParameterizedTypeBinding parBinding = (ParameterizedTypeBinding) refBinding;
					return new CollectionModel(model, typeFor(parBinding.arguments[0]));
				} else {
					var objectModel = modelForRef(model.bindingForJavaLangObject());
					return new CollectionModel(model, objectModel);
				}
			}
			/* other integer types */
			else if (JDTUtils.typeIsSubtypeOfName(refBinding, "java.lang.Integer")) {
				return intModel.get();
			} else if (JDTUtils.typeIsSubtypeOfName(refBinding, "java.math.BigInteger")) {
				return intModel.get();
			}
			/* other void types */
			else if (JDTUtils.typeIsSubtypeOfName(refBinding, "java.lang.Void")) {
				return voidModel.get();
			}
			/* rest */
			else if (typeBinding instanceof MissingTypeBinding) {
				Logger.warn("missing type binding: " + typeBinding.debugName());
				return new MissingModel(model, (MissingTypeBinding) typeBinding);
			}
			return modelForRef(refBinding);
		} else {
			return new EmptyModel(model, "incompatible type " + typeBinding);
		}
	}

	public TypeModel<?> typeFor(TypeReference typeReference) {
		return typeFor(typeReference.resolvedType);
	}





}
