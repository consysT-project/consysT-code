package de.tuda.stg.consys.invariants.subset.utils;

import de.tuda.stg.consys.invariants.subset.Logger;
import org.eclipse.jdt.internal.compiler.lookup.BaseTypeBinding;
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
			return nameOfClass((ReferenceBinding) binding).equals(typeName/* ~ "java.lang.Object" */);
		} else if (binding instanceof BaseTypeBinding) {
			BaseTypeBinding baseBinding = (BaseTypeBinding) binding;
			return String.valueOf(baseBinding.simpleName/* ~ "long" */).equals(typeName);
		}

		throw new UnsupportedOperationException("binding type not supported: " + binding);
	}

	public static String nameOfClass(ReferenceBinding refBinding) {
		return Arrays.stream(refBinding.compoundName).map(String::valueOf).reduce( (acc, e) -> acc + "." + e).orElse("");
	}

	public static boolean typeIsSubtypeOfName(TypeBinding binding, String typeName) {
		if (binding == null)
			throw new NullPointerException("binding was null");

		if (typeIsTypeOfName(binding, typeName)) {
			return true;
		}

		if (binding instanceof ReferenceBinding) {
			ReferenceBinding parent = null;
			try {
				parent = ((ReferenceBinding) binding).superclass();
			} catch (NullPointerException e) {
				//TODO: There is a null pointerexception sometimes in this code?
				Logger.err("there was a null pointer exception while getting the superclass for: " + binding.readableName());
				e.printStackTrace();
				return false;
			}

			if (parent == null) {
				return false;
			} else {
				return typeIsSubtypeOfName(parent, typeName);
			}
		} else {
			Logger.warn("unsupported binding: " + binding);
			return false;
		}
	}

	public static boolean methodMatchesSignature(MethodBinding binding, boolean isStatic, String declaringClassName, String methodName, String... argumentTypeNames) {
		if (binding.isStatic() != isStatic) {
			return false;
		}

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
