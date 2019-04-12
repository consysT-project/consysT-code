package de.tudarmstadt.consistency.demo.schema;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.replobj.japi.JRef;

import java.io.Serializable;

/**
 * Created on 05.03.19.
 *
 * @author Mirko Köhler
 */
public class ObjB implements Serializable {

	public int g;
	public JRef<@Strong ObjA> a;

	public ObjB(JRef<@Strong ObjA> a) {
		this.a = a;
		this.g = 0;
	}

	public String incG() {
		g = g + 1;
		return "done_bb";
	}

	public void incAll() {
		incG();
		a.invoke("inc"); //n1 / 0
		a.invoke("inc");
	}

	@Override
	public String toString() {
		return "ObjB(g = " + g + ", a = " + a + ")";
	}
}
