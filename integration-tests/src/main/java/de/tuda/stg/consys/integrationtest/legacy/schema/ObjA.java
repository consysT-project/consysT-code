package de.tuda.stg.consys.integrationtest.legacy.schema;

import java.io.Serializable;

/**
 * Created on 05.03.19.
 *
 * @author Mirko Köhler
 */
public class ObjA implements Serializable {

	public int f;

	public ObjA() {
		f = 0;
	}

	public String inc() {
		f = f + 1;
		return "done";
	}

	public int incBy(int x) {
		f = f + x;
		return f;
	}

	@Override
	public String toString() {
		return "ObjA(f = " + f + ")";
	}
}
