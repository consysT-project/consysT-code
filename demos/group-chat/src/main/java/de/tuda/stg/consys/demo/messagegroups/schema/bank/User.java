package de.tuda.stg.consys.demo.messagegroups.schema.bank;

import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;

import java.io.Serializable;

public class User implements Serializable {
	private @Immutable String name;

	public User(String name) {
		this.name = name;
	}
}
