package de.tuda.stg.consys.japi.legacy;

import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.core.legacy.ConsistencyLabel;

/**
 * Created on 14.03.19.
 *
 * @author Mirko Köhler
 */
public interface JConsistencyLevels {

	@Local ConsistencyLabel STRONG = ConsistencyLabel.Strong$.MODULE$;
	@Local ConsistencyLabel WEAK = ConsistencyLabel.Weak$.MODULE$;
	@Local ConsistencyLabel CAUSAL = ConsistencyLabel.Causal$.MODULE$;

	@Local ConsistencyLabel CMRDT = ConsistencyLabel.CmRDT$.MODULE$;
	@Local ConsistencyLabel CVRDT = ConsistencyLabel.CvRDT$.MODULE$;

}
