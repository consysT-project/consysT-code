package de.tuda.stg.consys.invariants.subset;

import com.google.common.collect.Lists;
import com.microsoft.z3.BoolSort;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Model;
import com.microsoft.z3.Status;
import de.tuda.stg.consys.invariants.subset.constraints.BaseClassConstraints;
import de.tuda.stg.consys.invariants.subset.model.BaseClassModel;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import org.eclipse.jdt.internal.compiler.lookup.MethodBinding;

import java.util.List;

public abstract class ClassProperties<CModel extends BaseClassModel, CConstraints extends BaseClassConstraints<CModel>> {

	protected final ProgramModel model;
	protected final CConstraints constraints;

	public ClassProperties(ProgramModel model, CConstraints constraints) {
		this.model = model;
		this.constraints = constraints;
	}

	protected abstract void addProperties(List<Property> properties);

	public BaseClassModel getClassModel() {
		return constraints.classModel;
	}

	public CheckResult check(Model z3Model) {
		List<Property> properties = Lists.newLinkedList();
		// Populates the list with properties
		addProperties(properties);


		var result = new CheckResult();
		for (var prop : properties) {
			var isValid = prop.check(z3Model);
			if (prop.name.equals("mergability/merge"))
				Logger.info("check");
			result.addResult(prop, isValid);
		}

		return result;
	}


	private boolean isValid(Model z3Model, Expr<BoolSort> expr) {
		model.solver.add(model.ctx.mkNot(expr));
		Status status = model.solver.check();


		switch (status) {
			case UNSATISFIABLE:
				return true;
			case SATISFIABLE:
				//System.out.println(expr);
				//System.out.println(solver.getModel());
				return false;
			case UNKNOWN:
				throw new RuntimeException("z3 was not able to solve the following expression. Reason: " + model.solver.getReasonUnknown() + "\n" + expr);
			default:
				//Does not exist
				throw new RuntimeException();
		}
	}


	private enum CheckStatus {
		VALID, INVALID, ERROR
	}



	public class CheckResult {
		private final List<PropertyResult> results = Lists.newLinkedList();

		void addResult(Property property, CheckStatus isValid) {
			results.add(new PropertyResult(property, isValid));
		}

		@Override
		public String toString() {
			StringBuilder builder = new StringBuilder();

			for (var res : results) {
				builder.append(res.property.description()).append(" : ").append(res.isValid).append("\n");
//				if (res.property instanceof ClassProperties.ClassProperty) {
//					builder.append(res.property.name).append(" : ").append(res.isValid).append("\n");
//				} else if (res.property instanceof ClassProperties.MethodProperty) {
//					builder.append(((MethodProperty) res.property).getMethodName()).append(" : ").append(res.property.name).append(" : ").append(res.isValid).append("\n");
//				}
			}

			return builder.toString();
		}

		private class PropertyResult {
			private final Property property;
			private final CheckStatus isValid;

			private PropertyResult(Property property, CheckStatus isValid) {
				this.property = property;
				this.isValid = isValid;
			}
		}
	}

	protected abstract class Property {
		private final String name;
		private final Expr<BoolSort> expr;

		Property(String name, Expr<BoolSort> expr) {
			this.name = name;
			this.expr = expr;
		}

		public CheckStatus check(Model z3Model) {
			try {
				Logger.info("Solving " + description() + "...");
				var result = isValid(z3Model, expr);
				Logger.info("Result = " + result /* + "\n" + model.solver.getStatistics() */);
				return result ? CheckStatus.VALID : CheckStatus.INVALID;
			} catch (RuntimeException e) {
//				throw new IllegalStateException("exception during solving for property <" + description() + ">\n" + expr + "\n", e);
				Logger.err("exception while checking property <" + description() + ">:");
				e.printStackTrace(Logger.err);
				return CheckStatus.ERROR;
			}
		}

		public Expr<BoolSort> getExpr() {
			return expr;
		}

		public String description() {
			return name;
		}
	}

	protected class ClassProperty extends Property {
		ClassProperty(String name, Expr<BoolSort> expr) {
			super(name, expr);
		}
	}

	protected class MethodProperty extends Property {
		private final MethodBinding binding;

		MethodProperty(String name, MethodBinding binding, Expr<BoolSort> expr) {
			super(name, expr);
			this.binding = binding;
		}

		@Override
		public String description() {
			return super.description() + "/" + String.valueOf(binding.selector);
		}
	}
}
