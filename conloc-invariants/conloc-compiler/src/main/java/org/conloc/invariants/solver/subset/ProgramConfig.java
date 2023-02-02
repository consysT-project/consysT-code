package org.conloc.invariants.solver.subset;

public class ProgramConfig {

	public final boolean MODEL__INCLUDE_IMPURE_METHODS;

	public final boolean SOLVER__CHECK_MERGE_PROPERTIES;
	public final boolean SOLVER__SIMPLE_NAMES;

	public final int SYSTEM__REPLICA_ID;
	public final String SYSTEM__REPLICA;
	public final int SYSTEM__NUM_OF_REPLICAS;

	public ProgramConfig(boolean model__include_impure_methods, boolean solver__check_merge_properties, boolean solver__simple_names, int system__replica_id, String system__replica, int system__num_of_replicas) {
		this.MODEL__INCLUDE_IMPURE_METHODS = model__include_impure_methods;
		SOLVER__CHECK_MERGE_PROPERTIES = solver__check_merge_properties;
		SOLVER__SIMPLE_NAMES = solver__simple_names;
		SYSTEM__REPLICA_ID = system__replica_id;
		SYSTEM__REPLICA = system__replica;
		SYSTEM__NUM_OF_REPLICAS = system__num_of_replicas;
	}
}
