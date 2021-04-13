package de.tuda.stg.consys.integrationtest.legacy.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.legacy.JRef;

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
		a.ref().inc();
	}

	@Override
	public String toString() {
		return "ObjB(g = " + g + ", a = " + a + ")";
	}
}
