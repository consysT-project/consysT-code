package de.tuda.stg.consys.compiler;


import com.sun.source.tree.*;
import com.sun.source.util.JavacTask;
import com.sun.source.util.Plugin;
import com.sun.source.util.TaskEvent;
import com.sun.source.util.TaskListener;
import com.sun.tools.javac.api.BasicJavacTask;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.TreeMaker;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Log;
import com.sun.tools.javac.util.Names;

import javax.lang.model.element.Name;
import javax.lang.model.type.TypeKind;
import java.util.List;
import java.util.Objects;
import java.util.Optional;


/**
 * Created on 30.09.19.
 *
 * @author Mirko Köhler
 */
public class ConsysJavacPlugin implements Plugin {

	public final static boolean DEBUG = false;

	@Override
	public String getName() {
		return "consys-compiler";
	}

	@Override
	public void init(JavacTask task, String... args) {
		Context context = ((BasicJavacTask) task).getContext();
		Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "using " + getName());

		task.addTaskListener(new TaskListener() {
			@Override
			public void started(TaskEvent taskEvent) {
			}

			@Override
			public void finished(TaskEvent taskEvent) {
				//We need to listen to the ANALYZE phase because we need type information
				if (taskEvent.getKind() != TaskEvent.Kind.ANALYZE) return;

				new ModifyingTreePathScanner(context) {

					@Override
					public Void visitMemberSelect(MemberSelectTree tree, Modificator mod) {
						//process children first
						Void result = super.visitMemberSelect(tree, mod);

						Optional<CRefUsage> maybeRefUsage = classifyRef(getCurrentPath(), context);
						if (maybeRefUsage.isPresent()) {
//							Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Path to ref: " + getCurrentPath());
//							Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Tree of ref: " + ((JCTree)tree));
//							Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Type of ref: " + ((JCTree)tree).type);
//							Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Sym of ref: " + ((JCTree.JCFieldAccess)tree).sym);

							CRefUsage refUsage = maybeRefUsage.get();


							if (refUsage instanceof CMethodInv) {
								CMethodInv methodInv = (CMethodInv) refUsage;

								TreeMaker factory = TreeMaker.instance(context);
								Names names = Names.instance(context);

								JCTree.JCExpression[] args = new JCTree.JCExpression[1 + methodInv.arguments.size()];
								args[0] = factory.Literal(methodInv.methodName.toString());
								for (int i = 1; i < args.length; i++) {
//									Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "i = " + i + ", length = " + args.length);
									args[i] = (JCTree.JCExpression) methodInv.arguments.get(i - 1);
								}

								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "old tree: " + tree);
								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "old type: " + ((JCTree)tree).type);
								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "old symbol: " + ((JCTree.JCFieldAccess)tree).sym);
								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "old symbol type: " + ((JCTree.JCFieldAccess)tree).sym.type);
								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "old symbol flags: " + Flags.asFlagSet(((JCTree.JCFieldAccess)tree).sym.flags()));


								JCTree.JCFieldAccess newSelect = factory.Select((JCTree.JCExpression) methodInv.expr, names.fromString("invoke"));

								//Type newType = Types.instance(context).createMethodTypeWithParameters(
								//		methodInv.type, methodInv.type.getParameterTypes().prepend(Symtab.instance(context).stringType));
								Type newType = Types.instance(context).createMethodTypeWithReturn(methodInv.type, Symtab.instance(context).objectType);
								Type.ArrayType arrayType = new Type.ArrayType(Symtab.instance(context).objectType, Symtab.instance(context).arrayClass);
								newType = Types.instance(context).createMethodTypeWithParameters(
										newType, com.sun.tools.javac.util.List.of(Symtab.instance(context).stringType, arrayType));

								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "new arg types: " + newType.getParameterTypes().toString(","));
								newSelect.setType(newType);

								newSelect.sym = //((JCTree.JCFieldAccess)tree).sym;
									new Symbol.MethodSymbol(Flags.PUBLIC | Flags.ABSTRACT, names.fromString("invoke"), newType, ((JCTree.JCFieldAccess)tree).sym.owner);
										//new Symbol.ClassSymbol(0L, names.fromString("de.tuda.stg.consys.objects.japi.Ref"), ((JCTree.JCFieldAccess) tree).selected.type,
										//		((JCTree.JCFieldAccess)tree).sym.owner.owner));

								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "new type: " + newType);
								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "new symbol: " + newSelect.sym);

								var argList = com.sun.tools.javac.util.List.from(args);
								JCTree.JCExpression arrayArg = factory.NewArray(factory.Type(Symtab.instance(context).objectType), com.sun.tools.javac.util.List.nil(), argList.tail);
								arrayArg.setType(arrayType);
								argList = com.sun.tools.javac.util.List.from(new JCTree.JCExpression[]{args[0], arrayArg});

								JCTree.JCMethodInvocation newInvoke = factory.at( ((JCTree) methodInv.originalPath.getLeaf()).pos )
								.Apply(null,
									newSelect,
									argList //com.sun.tools.javac.util.List.from(args)
								);
								newInvoke.type = ((JCTree) methodInv.originalPath.getLeaf()).type; // TODO: correct return type or must be Object?
								//newInvoke.type = newType.getReturnType();
								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "New invoke: " + newInvoke);
								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "New invoke type: " + newInvoke.type);

								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Old invoke: " + methodInv.originalPath.getLeaf());
//								Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Path: " + methodInv.originalPath);
								methodInv.originalPath.getModificator().accept(newInvoke);
								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "New invoke: " + newInvoke);
//
							} else if (refUsage instanceof CAssign) {
								CAssign assign = (CAssign) refUsage;

								TreeMaker factory = TreeMaker.instance(context);
								Names names = Names.instance(context);

								JCTree.JCFieldAccess newSelect = factory.Select((JCTree.JCExpression) assign.expr, names.fromString("setField"));

								JCTree.JCMethodInvocation newSetField = factory.at(((JCTree) assign.originalPath.getLeaf()).pos)
									.Apply(null,
										newSelect,
										com.sun.tools.javac.util.List.of(
											factory.Literal(assign.fieldName.toString()),
											(JCTree.JCExpression) assign.newValue
											)
									);

								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Old assign: " + assign.originalPath.getLeaf());
								//assign.originalPath.getModificator().accept(newSetField);
								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "New assign: " + newSetField);

							} else if (refUsage instanceof CFieldAcc) {
								CFieldAcc fieldAcc = (CFieldAcc) refUsage;

								TreeMaker factory = TreeMaker.instance(context);
								Names names = Names.instance(context);

								JCTree.JCFieldAccess newSelect = factory.Select((JCTree.JCExpression) fieldAcc.expr, names.fromString("getField"));

								JCTree.JCMethodInvocation newGetField = factory.at(((JCTree) fieldAcc.originalPath.getLeaf()).pos)
									.Apply(null,
										newSelect,
										com.sun.tools.javac.util.List.of(
											factory.Literal(fieldAcc.fieldName.toString())
										)
									);

								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Old access: " + fieldAcc.originalPath.getLeaf());
								//fieldAcc.originalPath.getModificator().accept(newGetField);
								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "New access: " + newGetField);

							}

							if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Unit after change: " + taskEvent.getCompilationUnit());
						}

						return result;
					}

				}
				//API Note: call scan method instead of Tree.accept to initialize the TreePathScanner
				.scan(taskEvent.getCompilationUnit(), null);

			}
		});
	}

	private static Optional<CRefUsage> classifyRef(ModifyingTreePath path, Context context) {
		if (path == null) {
			if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE,"Cannont classify ref for null\n=> empty1");
			return Optional.empty();
		}

		if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE,"# " + path.getLeaf());
		Tree curr = path.getLeaf();

		//Check for a call to ref(), i.e. there is a MemberSelect and a MethodInvocation
		if (!(curr instanceof MemberSelectTree
			&& ((MemberSelectTree) curr).getIdentifier().contentEquals("ref"))) {
			if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE,"=> empty1");
			return Optional.empty();
		}

		ExpressionTree expr = ((MemberSelectTree) curr).getExpression();
		//TODO: Types are not available in PARSE phase, but in ANALYZE phase we have to provide types when creating new expressions
//		Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Type of expr: " + ((JCTree.JCExpression) expr).type);

		//Move to parent leaf -> Ref.ref()
		path = path.getParentPath();
		if (path == null) {
			if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE,"=> empty2");
			return Optional.empty();
		}
		curr = path.getLeaf();

		if (!(curr instanceof MethodInvocationTree
			&& ((MethodInvocationTree) curr).getArguments().isEmpty()
			&& ((MethodInvocationTree) curr).getTypeArguments().isEmpty())) {
			if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE,"=> empty3");
			return Optional.empty();
		}

		//Move to parent leaf -> Ref.ref().method
		path = path.getParentPath();
		if (path == null) {
			if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE,"=> empty4");
			return Optional.empty();
		}
		curr = path.getLeaf();

		//Test if the ref belongs to a method invocation
		if (curr instanceof MemberSelectTree) {
			Name name = ((MemberSelectTree) curr).getIdentifier();

			// move to parent -> Ref.ref().method()
			ModifyingTreePath methodPath = path.getParentPath();
			if (methodPath == null) return Optional.empty();
			Tree methodCurr = methodPath.getLeaf();

			if (methodCurr instanceof MethodInvocationTree && ((MethodInvocationTree) methodCurr).getMethodSelect() == curr) {
				List<? extends ExpressionTree> args = ((MethodInvocationTree) methodCurr).getArguments();
				if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "=> method: " + expr + "." + name + "(" + args + ")");
				//Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "-- expr: " + methodCurr);
				//Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "-- Type of expr: " + ((JCTree.JCExpression) methodCurr).type);

				//Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "-- Type of expr: " + ((JCTree.JCExpression)expr).type);
				//Type.ClassType t = (Type.ClassType) ((JCTree.JCExpression)expr).type;


				return Optional.of(new CMethodInv(methodPath, expr, name, args, ((JCTree.JCFieldAccess)curr).type));
			}
		}

		//Test if the ref belongs to an assignment
		if (curr instanceof MemberSelectTree) {
			Name name = ((MemberSelectTree) curr).getIdentifier();

			ModifyingTreePath assignPath = path.getParentPath();
			if (assignPath == null) return Optional.empty();
			Tree assignCurr = assignPath.getLeaf();

			if (assignCurr instanceof AssignmentTree && ((AssignmentTree) assignCurr).getVariable() == curr) {
				if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "=> field set: " + expr + "." + name );
				return Optional.of(new CAssign(assignPath, expr, name, ((AssignmentTree) assignCurr).getExpression()));
			}
		}

		//Test if the ref belongs to a field access
		if (curr instanceof MemberSelectTree) {
			Name name = ((MemberSelectTree) curr).getIdentifier();
			if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "=> field get: " + expr + "." + name );
			return Optional.of(new CFieldAcc(path, expr, name));
		}

		if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE,"=> empty5");
		return Optional.empty();
	}


	private interface CRefUsage {
		ModifyingTreePath getOriginalPath();
	}

	private static class CMethodInv implements CRefUsage {
		private final ModifyingTreePath originalPath;
		final ExpressionTree expr;
		final Name methodName;
		final List<? extends ExpressionTree> arguments;
		final Type type;

		private CMethodInv(ModifyingTreePath originalPath, ExpressionTree expr, Name methodName, List<? extends ExpressionTree> arguments, Type type) {
			this.originalPath = originalPath;
			this.expr = expr;
			this.methodName = methodName;
			this.arguments = arguments;
			this.type = type;
		}

		@Override
		public ModifyingTreePath getOriginalPath() {
			return originalPath;
		}
	}

	private static class CAssign implements CRefUsage {
		private final ModifyingTreePath originalPath;
		final ExpressionTree expr;
		final Name fieldName;
		final ExpressionTree newValue;

		private CAssign(ModifyingTreePath originalPath, ExpressionTree expr, Name fieldName, ExpressionTree newValue) {
			this.originalPath = originalPath;
			this.expr = expr;
			this.fieldName = fieldName;
			this.newValue = newValue;
		}

		@Override
		public ModifyingTreePath getOriginalPath() {
			return originalPath;
		}
	}

	private static class CFieldAcc implements CRefUsage {
		private final ModifyingTreePath originalPath;
		final ExpressionTree expr;
		final Name fieldName;

		private CFieldAcc(ModifyingTreePath originalPath, ExpressionTree expr, Name fieldName) {
			this.originalPath = originalPath;
			this.expr = expr;
			this.fieldName = fieldName;
		}

		@Override
		public ModifyingTreePath getOriginalPath() {
			return originalPath;
		}
	}
}