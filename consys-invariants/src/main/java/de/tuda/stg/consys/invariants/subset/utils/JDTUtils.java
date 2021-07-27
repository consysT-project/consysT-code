package de.tuda.stg.consys.invariants.subset.utils;

import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;

import java.math.BigInteger;
import java.util.Arrays;

public class JDTUtils {

	/**
	 *
	 * @param binding
	 * @param typeName A name of the form "java.lang.Object"
	 * @return
	 */
	public static boolean typeIsTypeOfName(TypeBinding binding, String typeName) {

		if (binding instanceof ReferenceBinding) {
			var compundName = Arrays.stream(((ReferenceBinding) binding).compoundName).map(String::valueOf).reduce( (acc, e) -> acc + "." + e).orElse("");
			return compundName.equals(typeName/* ~ "java.lang.Object" */);
		}

		throw new UnsupportedOperationException("binding type not supported: " + binding);
	}

	public static boolean typeIsSubtypeOfName(TypeBinding binding, String typeName) {
		if (binding == null)
			throw new NullPointerException("binding was null.");

		if (typeIsTypeOfName(binding, typeName)) {
			return true;
		}

		if (binding instanceof ReferenceBinding) {
			ReferenceBinding parent = null;
			try {
				parent = ((ReferenceBinding) binding).superclass();
			} catch (NullPointerException e) {
				//TODO: There is a null pointerexception sometimes in this code?
				System.err.println("there was a null pointerexception while getting the superclass for: " + binding.readableName());
				e.printStackTrace();
				return false;
			}

			if (parent == null) {
				return false;
			} else {
				return typeIsSubtypeOfName(parent, typeName);
			}
		} else {
			System.err.println("unsupported binding: " + binding);
			return false;
		}
	}

	public static boolean methodMatchesSignature(MethodBinding binding, String declaringClassName, String methodName, String... argumentTypeNames) {
		if (!typeIsSubtypeOfName(binding.declaringClass, declaringClassName)) {
			return false;
		}

		if (!String.valueOf(binding.selector).equals(methodName)) {
			return false;
		}

		if (binding.parameters.length != argumentTypeNames.length) {
			return false;
		}

		for (int i = 0; i < argumentTypeNames.length; i++) {
			if (!typeIsTypeOfName(binding.parameters[i], argumentTypeNames[i])) {
				return false;
			}
		}

		return true;
	}
}
