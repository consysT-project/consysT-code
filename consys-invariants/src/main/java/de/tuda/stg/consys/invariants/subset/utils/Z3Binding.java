package de.tuda.stg.consys.invariants.subset.utils;

import com.microsoft.z3.*;

public class Z3Binding {

	public final Context ctx;
	public final Solver solver;


	public Z3Binding(Context ctx) {
		this.ctx = ctx;
		this.solver = ctx.mkSolver();
	}

	public Z3Binding() {
		this(new Context());
	}

	public boolean isValid(Expr<BoolSort> expr) {
		Status status = solver.check(ctx.mkNot(expr));
		switch (status) {
			case UNSATISFIABLE:
				return true;
			case SATISFIABLE:
				//System.out.println(expr);
				//System.out.println(solver.getModel());
				return false;
			case UNKNOWN:
				//throw new IllegalStateException("solving expression lead to an error: " + expr);
				System.err.println("Error solving " + expr);
				return false;
			default:
				//Does not exist
				throw new RuntimeException();
		}
	}


}
