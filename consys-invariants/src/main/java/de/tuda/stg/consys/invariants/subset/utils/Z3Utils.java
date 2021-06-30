package de.tuda.stg.consys.invariants.subset.utils;

import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.NameReference;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.lookup.*;

import java.util.Optional;
import java.util.function.Function;
import java.util.function.IntFunction;

public class Z3Utils {

	public static Optional<Sort> typeReferenceToSort(Context ctx, TypeReference typeReference) {
		return typeBindingToSort(ctx, typeReference.resolvedType);
	}

	/**
	 * Calls the correct visit method for the concrete type binding and returns the resulting Z3 Sort that describes
	 * the same type.
	 * @param typeBinding the type binding to translate
	 * @return the translated Z3 Sort, or empty if the typeBinding is void.
	 */
	public static Optional<Sort> typeBindingToSort(Context ctx, TypeBinding typeBinding) {
		if (typeBinding instanceof BaseTypeBinding) {
			BaseTypeBinding binding = (BaseTypeBinding) typeBinding;

			switch (binding.id) {
				case 2: // char
				case 3: // byte
				case 4: // short
				case 7: // long
				case 10: // int
					return Optional.of(ctx.getIntSort());
				case 8: // double
				case 9: // float
					return Optional.of(ctx.getRealSort());
				case 5: // boolean
					return Optional.of(ctx.getBoolSort());
				case 6: // void
					return Optional.empty();
				default:
					//throw new IllegalArgumentException("incompatible base type " + typeBinding);
					System.err.println("incompatible base type " + typeBinding);
					return Optional.empty();
			}
		} else if (typeBinding instanceof ArrayBinding) {
			ArrayBinding arrayBinding = (ArrayBinding) typeBinding;
			// translate element type
			Optional<Sort> elementType = typeBindingToSort(ctx, arrayBinding.leafComponentType);


			if (elementType.isEmpty()) {
//				throw new IllegalArgumentException("incompatible array element type in " + typeBinding);
				System.err.println("incompatible array element type in " + typeBinding);
				return Optional.empty();
			} else {
				// index type assumed to be integer
				Sort indexType = ctx.getIntSort();
				// build array sort from index and element type
				return Optional.of(ctx.mkArraySort(indexType, elementType.get()));
			}

		} else {
//			throw new IllegalArgumentException("incompatible type " + typeBinding);
			System.err.println("incompatible type " + typeBinding);
			return Optional.empty();
		}
	}

	public static Symbol[] mkSymbols(Context ctx, String[] strings) {
		if (strings == null) {
			return null;
		} else {
			Symbol[] symbols = new Symbol[strings.length];

			for(int i = 0; i < strings.length; ++i) {
				symbols[i] = ctx.mkSymbol(strings[i]);
			}
			return symbols;
		}
	}

	public static <T> Optional<T> findBindingInArray(T[] arr, Binding binding, Function<T, Binding> getBinding) {
		if (binding == null) {
			throw new IllegalArgumentException("binding was null");
		}

		for (T elem : arr) {
			if (binding.equals(getBinding.apply(elem)))	return Optional.of(elem);
		}
		return Optional.empty();
	}


	public static <T> Optional<T> findReferenceInArray(T[] arr, Reference ref, Function<T, Binding> getBinding) {
		Binding binding = null;
		if (ref instanceof NameReference) {
			NameReference nameReference = (NameReference) ref;
			if (nameReference.binding instanceof FieldBinding) {
				binding = nameReference.fieldBinding();
			} else if (nameReference.binding instanceof LocalVariableBinding) {
				binding =nameReference.localVariableBinding();
			}
		} else if (ref instanceof FieldReference) {
			binding = ref.fieldBinding();
		}

		if (binding == null)
			return Optional.empty();

		return findBindingInArray(arr, binding, getBinding);
	}

	public static <T> T[] arrayPrepend(IntFunction<T[]> arrSupplier, T[] src, T... elems) {
		T[] newArr = arrSupplier.apply(src.length + elems.length);
		System.arraycopy(src, 0, newArr, elems.length, src.length);
		System.arraycopy(elems, 0, newArr, 0, elems.length);

		return newArr;
	}



}
