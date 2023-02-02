package org.conloc.invariants.solver.subset.utils;

import com.microsoft.z3.Context;
import com.microsoft.z3.Symbol;
import org.eclipse.jdt.internal.compiler.ast.FieldReference;
import org.eclipse.jdt.internal.compiler.ast.NameReference;
import org.eclipse.jdt.internal.compiler.ast.Reference;
import org.eclipse.jdt.internal.compiler.lookup.Binding;
import org.eclipse.jdt.internal.compiler.lookup.FieldBinding;
import org.eclipse.jdt.internal.compiler.lookup.LocalVariableBinding;

import java.util.Optional;
import java.util.function.Function;
import java.util.function.IntFunction;

public class Z3Utils {

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
