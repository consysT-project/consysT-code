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
import java.util.List;
import java.util.Optional;


/**
 * Created on 30.09.19.
 *
 * @author Mirko Köhler
 */
public class ConsysJavacPlugin implements Plugin {

	public final static boolean DEBUG = true;
	static Log logger;

	@Override
	public String getName() {
		return "consys-compiler";
	}

	@Override
	public void init(JavacTask task, String... args) {
		Context context = ((BasicJavacTask) task).getContext();
		ConsysJavacPlugin.logger = Log.instance(context);

		log("using " + getName());

		task.addTaskListener(new TaskListener() {
			@Override
			public void started(TaskEvent taskEvent) {}

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
							//logDebug("Path to ref: " + getCurrentPath());
							//logDebug("Tree of ref: " + tree);
							//logDebug("Type of ref: " + ((JCTree)tree).type);
							//logDebug("Sym of ref: " + ((JCTree.JCFieldAccess)tree).sym);

							TreeMaker factory = TreeMaker.instance(context);
							Names names = Names.instance(context);
							Types types = Types.instance(context);
							Symtab symtab = Symtab.instance(context);

							CRefUsage refUsage = maybeRefUsage.get();
							if (refUsage instanceof CMethodInv) {
								CMethodInv methodInv = (CMethodInv) refUsage;
								Type originalReturnType = ((JCTree) methodInv.originalPath.getLeaf()).type;

								JCTree.JCFieldAccess newSelect = factory.Select((JCTree.JCExpression) methodInv.expr, names.fromString("invoke"));

								// adapt old 'Ref.ref()' to new 'Ref.invoke(String, Object[])' method type
								Type selectType = types.createMethodTypeWithReturn(methodInv.memberSelectType, originalReturnType);
								selectType = types.createMethodTypeWithParameters(selectType,
										com.sun.tools.javac.util.List.of(
												symtab.stringType,
												// we must directly construct the transformed form of the varargs parameter type, i.e. Object[]
												new Type.ArrayType(symtab.objectType, symtab.arrayClass)));
								newSelect.setType(selectType);

								newSelect.sym = ((JCTree.JCFieldAccess)tree).sym.owner.members().findFirst(names.fromString("invoke"));

								// construct invocation arguments in transformed form of varargs, i.e. Objects... -> new Object[]{...}
								JCTree.JCExpression arrayArg = factory.NewArray(
										factory.Type(symtab.objectType),
										com.sun.tools.javac.util.List.nil(),
										com.sun.tools.javac.util.List.from(methodInv.arguments.toArray(new JCTree.JCExpression[0])));
								arrayArg.setType(new Type.ArrayType(symtab.objectType, symtab.arrayClass));

								// explicitly re-construct annotations of the return type for annotating the <>invoke() type parameter
								com.sun.tools.javac.util.List<Attribute.Compound> returnTypeAnnotations = com.sun.tools.javac.util.List.nil();
								for (var elem : ((TypeMetadata.Annotations)originalReturnType.getMetadataOfKind(TypeMetadata.Entry.Kind.ANNOTATIONS)).getAnnotations())
									returnTypeAnnotations = returnTypeAnnotations.append(elem);

								JCTree.JCMethodInvocation newInvoke = factory.at( ((JCTree) methodInv.originalPath.getLeaf()).pos )
								.Apply(com.sun.tools.javac.util.List.of(factory.AnnotatedType(factory.Annotations(returnTypeAnnotations), factory.Type(originalReturnType))),
										newSelect,
										com.sun.tools.javac.util.List.of(factory.Literal(methodInv.methodName.toString()), arrayArg)
								);

								newInvoke.setType(originalReturnType);

								logDebug("Old invoke: " + methodInv.originalPath.getLeaf());
								methodInv.originalPath.getModificator().accept(newInvoke);
								logDebug("New invoke: " + newInvoke);
//
							} else if (refUsage instanceof CAssign) {
								CAssign assign = (CAssign) refUsage;

								JCTree.JCFieldAccess newSelect = factory.Select((JCTree.JCExpression) assign.expr, names.fromString("setField"));
								// TODO: set type and symbol for newSelect

								JCTree.JCMethodInvocation newSetField = factory.at(((JCTree) assign.originalPath.getLeaf()).pos)
									.Apply(null,
										newSelect,
										com.sun.tools.javac.util.List.of(
											factory.Literal(assign.fieldName.toString()),
											(JCTree.JCExpression) assign.newValue
											)
									);
								// TODO: set type for newSetField

								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Old assign: " + assign.originalPath.getLeaf());
								//assign.originalPath.getModificator().accept(newSetField); // TODO
								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "New assign: " + newSetField);

							} else if (refUsage instanceof CFieldAcc) {
								CFieldAcc fieldAcc = (CFieldAcc) refUsage;

								JCTree.JCFieldAccess newSelect = factory.Select((JCTree.JCExpression) fieldAcc.expr, names.fromString("getField"));
								// TODO: set type and symbol for newSelect

								JCTree.JCMethodInvocation newGetField = factory.at(((JCTree) fieldAcc.originalPath.getLeaf()).pos)
									.Apply(null,
										newSelect,
										com.sun.tools.javac.util.List.of(
											factory.Literal(fieldAcc.fieldName.toString())
										)
									);
								// TODO: set type for newGetField

								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "Old access: " + fieldAcc.originalPath.getLeaf());
								//fieldAcc.originalPath.getModificator().accept(newGetField); // TODO
								if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE, "New access: " + newGetField);

							}

							//logDebug("Unit after change: " + taskEvent.getCompilationUnit());
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
			logDebug("Cannont classify ref for null\n=> empty1");
			return Optional.empty();
		}

		//logDebug("# " + path.getLeaf());
		Tree curr = path.getLeaf();

		//Check for a call to ref(), i.e. there is a MemberSelect and a MethodInvocation
		if (!(curr instanceof MemberSelectTree
			&& ((MemberSelectTree) curr).getIdentifier().contentEquals("ref"))) {
			//logDebug("=> empty1");
			return Optional.empty();
		}

		ExpressionTree expr = ((MemberSelectTree) curr).getExpression();

		//Move to parent leaf, i.e. Ref.ref()
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

		//Move to parent leaf, i.e Ref.ref().method
		path = path.getParentPath();
		if (path == null) {
			if (DEBUG) Log.instance(context).printRawLines(Log.WriterKind.NOTICE,"=> empty4");
			return Optional.empty();
		}
		curr = path.getLeaf();

		//Test if the ref belongs to a method invocation
		if (curr instanceof MemberSelectTree) {
			Name name = ((MemberSelectTree) curr).getIdentifier();

			// move to parent, i.e. Ref.ref().method()
			ModifyingTreePath methodPath = path.getParentPath();
			if (methodPath == null) return Optional.empty();
			Tree methodCurr = methodPath.getLeaf();

			if (methodCurr instanceof MethodInvocationTree && ((MethodInvocationTree) methodCurr).getMethodSelect() == curr) {
				List<? extends ExpressionTree> args = ((MethodInvocationTree) methodCurr).getArguments();
				logDebug("=> method: " + expr + "." + name + "(" + args + ")");

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

	private static void log(String msg) {
		logger.printRawLines(Log.WriterKind.NOTICE, msg);
	}

	private static void logDebug(String msg) {
		if (DEBUG) logger.printRawLines(Log.WriterKind.NOTICE, msg);
	}

	private interface CRefUsage {
		ModifyingTreePath getOriginalPath();
	}

	private static class CMethodInv implements CRefUsage {
		private final ModifyingTreePath originalPath;
		final ExpressionTree expr;
		final Name methodName;
		final List<? extends ExpressionTree> arguments;
		/** Executable type of the 'Ref.ref' member-select-tree **/
		final Type memberSelectType;

		private CMethodInv(ModifyingTreePath originalPath, ExpressionTree expr, Name methodName,
						   List<? extends ExpressionTree> arguments, Type memberSelectType) {
			this.originalPath = originalPath;
			this.expr = expr;
			this.methodName = methodName;
			this.arguments = arguments;
			this.memberSelectType = memberSelectType;
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