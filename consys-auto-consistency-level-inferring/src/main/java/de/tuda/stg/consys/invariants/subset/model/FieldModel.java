package de.tuda.stg.consys.invariants.subset.model;

import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;
import de.tuda.stg.consys.invariants.subset.Lazy;
import org.eclipse.jdt.internal.compiler.ast.FieldDeclaration;
import scala.runtime.LazyRef;

public class FieldModel {

	private final Context ctx;
	private final FieldDeclaration field;

	private final Lazy<String> name;
	private final Lazy<Sort> sort;


	public FieldModel(Context ctx, FieldDeclaration field) {
		this.ctx = ctx;
		this.field = field;
		this.name = Lazy.make(() -> String.valueOf(field.name));
		this.sort = Lazy.make(() -> Z3Utils.typeReferenceToSort(ctx, field.type));
	}

	public String getName() {
		return name.get();
	}

	public Sort getSort() {
		return sort.get();
	}
}
