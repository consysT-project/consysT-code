package de.tuda.stg.consys.compiler;


import com.sun.source.tree.*;
import com.sun.source.util.JavacTask;
import com.sun.source.util.Plugin;
import com.sun.source.util.TaskEvent;
import com.sun.source.util.TaskListener;
import com.sun.tools.javac.api.BasicJavacTask;
import com.sun.tools.javac.code.*;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
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

				//API Note: call scan method instead of Tree.accept to initialize the TreePathScanner
				new RefModifyingTreePathScanner(context).scan(taskEvent.getCompilationUnit(), null);
			}
		});
	}

	private static class RefModifyingTreePathScanner extends ModifyingTreePathScanner {
		private final TreeMaker factory;
		private final Names names;
		private final Types types;
		private final Symtab symtab;

		RefModifyingTreePathScanner(Context context) {
			super(context);
			factory = TreeMaker.instance(context);
			names = Names.instance(context);
			types = Types.instance(context);
			symtab = Symtab.instance(context);
		}

		@Override
		public Void visitMemberSelect(MemberSelectTree tree, Modificator mod) {
			//process children first
			Void result = super.visitMemberSelect(tree, mod);

			Optional<CRefUsage> maybeRefUsage = classifyRef(getCurrentPath(), context);
			if (maybeRefUsage.isPresent()) {
				//logDebug("Path to ref: " + getCurrentPath());
				//logDebug("Tree of ref: " + tree);
				//logDebug("Type of ref: " + ((JCTree)tree).type);
				//logDebug("Sym of ref: " + ((JCFieldAccess)tree).sym);

				CRefUsage refUsage = maybeRefUsage.get();
				if (refUsage instanceof CMethodInv) {
					CMethodInv methodInv = (CMethodInv) refUsage;
					Type originalReturnType = ((JCTree) methodInv.originalPath.getLeaf()).type;

					JCTree.JCFieldAccess newSelect = factory.Select((JCExpression) methodInv.expr, names.fromString("invoke"));

					// adapt old 'Ref.ref()' to new 'Ref.invoke(String, Object[])' method type
					Type selectType = types.createMethodTypeWithReturn(methodInv.refMemberSelectType, originalReturnType);
					selectType = types.createMethodTypeWithParameters(selectType,
							com.sun.tools.javac.util.List.of(
									symtab.stringType,
									// we must directly construct the transformed form of the varargs parameter type, i.e. Object[]
									new Type.ArrayType(symtab.objectType, symtab.arrayClass)));
					newSelect.setType(selectType);

					newSelect.sym = ((JCFieldAccess)tree).sym.owner.members().findFirst(names.fromString("invoke"));

					// construct invocation arguments in transformed form of varargs, i.e. Objects... -> new Object[]{...}
					JCExpression arrayArg = factory.NewArray(
							factory.Type(symtab.objectType),
							com.sun.tools.javac.util.List.nil(),
							com.sun.tools.javac.util.List.from(methodInv.arguments.toArray(new JCTree.JCExpression[0])));
					arrayArg.setType(new Type.ArrayType(symtab.objectType, symtab.arrayClass));

					// construct new Ref.<...>invoke("...", new Object[]{...}) expression
					JCMethodInvocation newInvoke = factory.at( ((JCTree) methodInv.originalPath.getLeaf()).pos )
							.Apply(typeArgTreeFromType(originalReturnType),
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
					Type originalFieldType = ((JCTree) assign.originalPath.getLeaf()).type;

					JCFieldAccess newSelect = factory.Select((JCExpression) assign.expr, names.fromString("setField"));

					// adapt old 'Ref.ref()' to new 'Ref.setField(String, R)' method type
					Type selectType = types.createMethodTypeWithReturn(assign.refMemberSelectType, symtab.voidType);
					selectType = types.createMethodTypeWithParameters(selectType,
							com.sun.tools.javac.util.List.of(symtab.stringType, originalFieldType));
					newSelect.setType(selectType);

					newSelect.sym = ((JCFieldAccess)tree).sym.owner.members().findFirst(names.fromString("setField"));

					// construct new Ref.<...>setField("...", ...) expression
					JCMethodInvocation newSetField = factory.at(((JCTree) assign.originalPath.getLeaf()).pos)
							.Apply(typeArgTreeFromType(originalFieldType),
									newSelect,
									com.sun.tools.javac.util.List.of(
											factory.Literal(assign.fieldName.toString()),
											(JCExpression) assign.newValue)
							);
					newSetField.setType(symtab.voidType);

					logDebug("Old assign: " + assign.originalPath.getLeaf());
					assign.originalPath.getModificator().accept(newSetField);
					logDebug("New assign: " + newSetField);

				} else if (refUsage instanceof CFieldAcc) {
					CFieldAcc fieldAcc = (CFieldAcc) refUsage;
					Type originalFieldType = ((JCTree) fieldAcc.originalPath.getLeaf()).type;

					JCFieldAccess newSelect = factory.Select((JCExpression) fieldAcc.expr, names.fromString("getField"));

					// adapt old 'Ref.ref()' to new 'Ref.getField(String)' method type
					Type selectType = types.createMethodTypeWithReturn(fieldAcc.refMemberSelectType, originalFieldType);
					selectType = types.createMethodTypeWithParameters(selectType,
							com.sun.tools.javac.util.List.of(symtab.stringType));
					newSelect.setType(selectType);

					newSelect.sym = ((JCFieldAccess)tree).sym.owner.members().findFirst(names.fromString("getField"));

					JCMethodInvocation newGetField = factory.at(((JCTree) fieldAcc.originalPath.getLeaf()).pos)
							.Apply(typeArgTreeFromType(originalFieldType),
									newSelect,
									com.sun.tools.javac.util.List.of(factory.Literal(fieldAcc.fieldName.toString()))
							);
					newGetField.setType(originalFieldType);

					logDebug("Old access: " + fieldAcc.originalPath.getLeaf());
					fieldAcc.originalPath.getModificator().accept(newGetField);
					logDebug("New access: " + newGetField);
				}

				//logDebug("Unit after change: " + taskEvent.getCompilationUnit());
			}

			return result;
		}

		private com.sun.tools.javac.util.List<JCTree.JCExpression> typeArgTreeFromType(Type type) {
			TypeMetadata.Annotations metadata = ((TypeMetadata.Annotations) type.getMetadataOfKind(TypeMetadata.Entry.Kind.ANNOTATIONS));
			if (metadata == null) {
				return null;
			}

			com.sun.tools.javac.util.List<Attribute.Compound> annotations = com.sun.tools.javac.util.List.nil();
			for (var elem : metadata.getAnnotations()) {
				annotations = annotations.append(elem);
			}
			com.sun.tools.javac.util.List<JCAnnotation> annotationTrees = factory.Annotations(annotations);

			com.sun.tools.javac.util.List<JCAnnotation> i = annotationTrees;
			com.sun.tools.javac.util.List<Attribute.Compound> j = annotations;
			while (i.nonEmpty()) {
				i.head.attribute = j.head;
				i = i.tail;
				j = j.tail;
			}

			return com.sun.tools.javac.util.List.of(factory.AnnotatedType(annotationTrees, factory.Type(type)));
		}
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
		Type refSelectType = ((JCTree.JCFieldAccess) curr).type;

		//Move to parent leaf, i.e. Ref.ref()
		path = path.getParentPath();
		if (path == null) {
			logDebug("=> empty2");
			return Optional.empty();
		}
		curr = path.getLeaf();

		if (!(curr instanceof MethodInvocationTree
			&& ((MethodInvocationTree) curr).getArguments().isEmpty()
			&& ((MethodInvocationTree) curr).getTypeArguments().isEmpty())) {
			logDebug("=> empty3");
			return Optional.empty();
		}

		//Move to parent leaf, i.e Ref.ref().member
		path = path.getParentPath();
		if (path == null) {
			logDebug("=> empty4");
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

				return Optional.of(new CMethodInv(methodPath, expr, name, args, refSelectType));
			}
		}

		//Test if the ref belongs to an assignment
		if (curr instanceof MemberSelectTree) {
			Name name = ((MemberSelectTree) curr).getIdentifier();

			ModifyingTreePath assignPath = path.getParentPath();
			if (assignPath == null) return Optional.empty();
			Tree assignCurr = assignPath.getLeaf();

			if (assignCurr instanceof AssignmentTree && ((AssignmentTree) assignCurr).getVariable() == curr) {
				logDebug("=> field set: " + expr + "." + name);
				return Optional.of(new CAssign(assignPath, expr, name, ((AssignmentTree) assignCurr).getExpression(), refSelectType));
			}
		}

		//Test if the ref belongs to a field access
		if (curr instanceof MemberSelectTree) {
			Name name = ((MemberSelectTree) curr).getIdentifier();
			logDebug("=> field get: " + expr + "." + name);
			return Optional.of(new CFieldAcc(path, expr, name, refSelectType));
		}

		logDebug("=> empty5");
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
		Type refMemberSelectType;

		private CMethodInv(ModifyingTreePath originalPath, ExpressionTree expr, Name methodName,
						   List<? extends ExpressionTree> arguments, Type refMemberSelectType) {
			this.originalPath = originalPath;
			this.expr = expr;
			this.methodName = methodName;
			this.arguments = arguments;
			this.refMemberSelectType = refMemberSelectType;
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
		/** Executable type of the 'Ref.ref' member-select-tree **/
		Type refMemberSelectType;

		private CAssign(ModifyingTreePath originalPath, ExpressionTree expr, Name fieldName,
						ExpressionTree newValue, Type refMemberSelectType) {
			this.originalPath = originalPath;
			this.expr = expr;
			this.fieldName = fieldName;
			this.newValue = newValue;
			this.refMemberSelectType = refMemberSelectType;
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
		/** Executable type of the 'Ref.ref' member-select-tree **/
		Type refMemberSelectType;

		private CFieldAcc(ModifyingTreePath originalPath, ExpressionTree expr, Name fieldName, Type refMemberSelectType) {
			this.originalPath = originalPath;
			this.expr = expr;
			this.fieldName = fieldName;
			this.refMemberSelectType = refMemberSelectType;
		}

		@Override
		public ModifyingTreePath getOriginalPath() {
			return originalPath;
		}
	}
}