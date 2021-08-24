package de.tuda.stg.consys.invariants.subset.utils;

import de.tuda.stg.consys.invariants.subset.Logger;
import org.eclipse.jdt.internal.compiler.lookup.*;

import java.util.Arrays;

public class JDTUtils {

	public static FieldBinding erase(FieldBinding binding) {
		return binding.original();
	}

	public static ReferenceBinding erase(ReferenceBinding binding) {
		return (ReferenceBinding) binding.original();
	}

	public static MethodBinding erase(MethodBinding binding) {
		return binding.original();
	}

	/**
	 *
	 * @param binding
	 * @param typeName A name of the form "java.lang.Object"
	 * @return
	 */
	public static boolean typeIsTypeOfName(TypeBinding binding, String typeName) {

		if (binding instanceof ReferenceBinding) {
			return typeName/* ~ "java.lang.Object" */.equals(nameOfClass((ReferenceBinding) binding));
		} else if (binding instanceof BaseTypeBinding) {
			BaseTypeBinding baseBinding = (BaseTypeBinding) binding;
			return String.valueOf(baseBinding.simpleName/* ~ "long" */).equals(typeName);
		}

		throw new UnsupportedOperationException("binding type not supported: " + binding);
	}

	public static String nameOfClass(ReferenceBinding refBinding) {
		if (refBinding instanceof TypeVariableBinding) {
			return nameOfClass(((TypeVariableBinding) refBinding).superclass);
		} else {
			return Arrays.stream(erase(refBinding).compoundName).map(String::valueOf).reduce( (acc, e) -> acc + "." + e).orElse("");
		}

	}

	public static String simpleNameOfClass(ReferenceBinding refBinding) {
		return String.valueOf(refBinding.shortReadableName());
	}

	public static boolean typeIsSubtypeOfName(TypeBinding binding, String typeName) {
		if (binding == null)
			throw new NullPointerException("binding was null");

		if (typeIsTypeOfName(binding, typeName)) {
			return true;
		}

		if (binding instanceof ReferenceBinding) {
			ReferenceBinding refBinding = (ReferenceBinding) binding;
			ReferenceBinding parent = null;
			try {
				parent = refBinding.superclass();
			} catch (NullPointerException e) {
				//TODO: There is a null pointerexception sometimes in this code?
				Logger.err("there was a null pointer exception while getting the superclass for: " + binding.debugName());
				e.printStackTrace(Logger.err);
			}

			// Check super class
			var parentMatches = false;
			if (parent != null) {
				parentMatches = typeIsSubtypeOfName(parent, typeName);
			}
			if (parentMatches) {
				return true;
			}

			// Check all super interfaces
			if (refBinding.superInterfaces() == null) {
				return false;
			}

			var interfaceMatches = false;
			for (var superInterface : refBinding.superInterfaces()) {
				interfaceMatches = interfaceMatches || typeIsSubtypeOfName(superInterface, typeName);
			}
			return interfaceMatches;

		} else {
			Logger.warn("unsupported binding: " + binding);
			return false;
		}
	}

	public static boolean methodMatchesSignature(TypeBinding receiverBinding, MethodBinding binding, boolean isStatic, String declaringClassName, String methodName, String... argumentTypeNames) {
		if (binding.isStatic() != isStatic) {
			return false;
		}

		if (!typeIsSubtypeOfName(receiverBinding, declaringClassName)) {
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
