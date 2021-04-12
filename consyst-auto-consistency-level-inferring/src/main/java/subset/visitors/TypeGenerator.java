package subset.visitors;

import com.microsoft.z3.Sort;
import org.eclipse.jdt.internal.compiler.ast.TypeReference;
import org.eclipse.jdt.internal.compiler.lookup.ArrayBinding;
import org.eclipse.jdt.internal.compiler.lookup.BaseTypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.jmlspecs.jml4.ast.JmlArrayTypeReference;
import org.jmlspecs.jml4.ast.JmlSingleTypeReference;
import subset.Z3Checker;

/**
 * This visitor is used to translate Java type references to Z3 Sorts. For example, in order to create an
 * {@link subset.z3_model.InternalVar} object, the type of the variable is determined using this class.
 * Note that Java types are usually described using {@link TypeReference} objects. However, the actual
 * type information lies within their {@link TypeBinding}. That's why type references are first resolved and
 * then the resulting type binding visited again.
 */
public class TypeGenerator {

  /*
   ******************************************** Type References ***************************************
   */

  /**
   * Calls the correct visit method for the actual subtype of the argument in order to translate the type
   * reference to a Z3 Sort. Only primitive types and
   * array types of primitive types are supported currently.
   * @param typeReference the type reference to translate
   * @return the resulting Z3 Sort from the visit calls or {@code null} if the type is not supported
   */
  public Sort visitTypeReference(TypeReference typeReference) {

    if (typeReference instanceof  JmlSingleTypeReference) {
      return visitJmlSingleTypeReference((JmlSingleTypeReference) typeReference);
    }
    else if(typeReference instanceof JmlArrayTypeReference) {
      return visitJmlArrayTypeReference((JmlArrayTypeReference) typeReference);
    }
    return null;
  }

  public Sort visitJmlSingleTypeReference(JmlSingleTypeReference singleTypeReference) {
    return visitTypeBinding(singleTypeReference.resolvedType);
  }

  public Sort visitJmlArrayTypeReference(JmlArrayTypeReference arrayTypeReference) {
    return visitTypeBinding(arrayTypeReference.resolvedType);
  }


  /*
  ***************************************** Type Bindings **********************************************
   */

  /**
   * Calls the correct visit method for the concrete type binding and returns the resulting Z3 Sort that describes
   * the same type.
   * @param typeBinding the type binding to translate
   * @return the translated Z3 Sort or {@code null}, if the type binding is not supported
   */
  public Sort visitTypeBinding(TypeBinding typeBinding) {
    if (typeBinding instanceof BaseTypeBinding)
      return visitBaseTypeBinding((BaseTypeBinding) typeBinding);
    else if (typeBinding instanceof ArrayBinding)
      return visitArrayBinding((ArrayBinding) typeBinding);
    return null;
  }

  /**
   * Visits type bindings of primitive types like {@code int}, or {@code boolean} and translates them into their
   * Z3 correspondence.
   * See {@link TypeBinding} for the Java compiler's representation of primitive types.
   * @param binding the primitive type to translate
   * @return the corresponding Z3 Sort
   */
  public Sort visitBaseTypeBinding(BaseTypeBinding binding) {
    switch (binding.id) {
      case 2: // char
      case 3: // byte
      case 4: // short
      case 7: // long
      case 10: // int
        return Z3Checker.context.getIntSort();
      case 8: // double
      case 9: // float
        return Z3Checker.context.getRealSort();
      case 5: // boolean
        return Z3Checker.context.getBoolSort();
      default:
        return null;
    }
  }

  /**
   * Visits type bindings of array types like {@code int[]} and translates them to their Z3 correspondence.
   * @param arrayBinding the array type to translate
   * @return the corresponding Z3 Sort
   */
  public Sort visitArrayBinding(ArrayBinding arrayBinding) {
    // translate element type
    Sort elementType = visitTypeBinding(arrayBinding.leafComponentType);

    // index type assumed to be integer
    Sort indexType = Z3Checker.context.getIntSort();

    // build array sort from index and element type
    return Z3Checker.context.mkArraySort(indexType, elementType);
  }
}
