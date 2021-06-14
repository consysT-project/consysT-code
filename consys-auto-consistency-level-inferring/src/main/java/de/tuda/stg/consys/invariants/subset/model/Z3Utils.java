package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Symbol;
import de.tuda.stg.consys.invariants.subset.Z3Checker;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.BaseTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlArrayTypeReference;
import org.jmlspecs.jml4.ast.JmlSingleTypeReference;

public class Z3Utils {

	public static Sort typeReferenceToSort(Context ctx, TypeReference typeReference) {
		return typeBindingToSort(ctx, typeReference.resolvedType);
	}

	/**
	 * Calls the correct visit method for the concrete type binding and returns the resulting Z3 Sort that describes
	 * the same type.
	 * @param typeBinding the type binding to translate
	 * @return the translated Z3 Sort, or null if the typeBinding is void.
	 */
	public static Sort typeBindingToSort(Context ctx, TypeBinding typeBinding) {
		if (typeBinding instanceof BaseTypeBinding) {
			BaseTypeBinding binding = (BaseTypeBinding) typeBinding;

			switch (binding.id) {
				case 2: // char
				case 3: // byte
				case 4: // short
				case 7: // long
				case 10: // int
					return ctx.getIntSort();
				case 8: // double
				case 9: // float
					return ctx.getRealSort();
				case 5: // boolean
					return ctx.getBoolSort();
				case 6: // void
					return null;
				default:
					throw new IllegalArgumentException("incompatible base type " + typeBinding);
			}
		} else if (typeBinding instanceof ArrayBinding) {
			ArrayBinding arrayBinding = (ArrayBinding) typeBinding;
			// translate element type
			Sort elementType = typeBindingToSort(ctx, arrayBinding.leafComponentType);

			// index type assumed to be integer
			Sort indexType = Z3Checker.context.getIntSort();

			// build array sort from index and element type
			return Z3Checker.context.mkArraySort(indexType, elementType);
		} else {
			throw new IllegalArgumentException("incompatible type " + typeBinding);
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

}
