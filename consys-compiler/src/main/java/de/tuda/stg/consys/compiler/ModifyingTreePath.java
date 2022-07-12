package de.tuda.stg.consys.compiler;

import com.sun.source.tree.Tree;

/**
 * Created on 01.10.19.
 *
 * @author Mirko Köhler
 */
public class ModifyingTreePath {
	private final Tree leaf;
	private final ModifyingTreePathScanner.Modificator mod;

	private final ModifyingTreePath parent;


	public ModifyingTreePath(ModifyingTreePath parent, Tree leaf, ModifyingTreePathScanner.Modificator mod) {
		this.leaf = leaf;
		this.mod = mod;
		this.parent = parent;
	}

	public Tree getLeaf() {
		return this.leaf;
	}

	public ModifyingTreePathScanner.Modificator getModificator() {
		return this.mod;
	}

	public ModifyingTreePath getParentPath() {
		return this.parent;
	}

	@Override
	public String toString() {
		String parentString = parent == null ? "|---" : parent.toString();
		return parentString + " --- " + leaf.toString();
	}

}
