package de.tuda.stg.consys.japi;

import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.core.store.legacy.ConsistencyLabel;

/**
 * Created on 14.03.19.
 *
 * @author Mirko Köhler
 */
public interface JConsistencyLevels {

	@Local ConsistencyLabel STRONG = ConsistencyLabel.Strong$.MODULE$;
	@Local ConsistencyLabel WEAK = ConsistencyLabel.Weak$.MODULE$;
	@Local ConsistencyLabel CAUSAL = ConsistencyLabel.Causal$.MODULE$;

}
