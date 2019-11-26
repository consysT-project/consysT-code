package de.tuda.stg.consys.japi;

import de.tuda.stg.consys.core.ConsistencyLevel;
import de.tuda.stg.consys.checker.qual.Local;

/**
 * Created on 14.03.19.
 *
 * @author Mirko Köhler
 */
public interface JConsistencyLevels {

	@Local ConsistencyLevel STRONG = ConsistencyLevel.Strong$.MODULE$;
	@Local ConsistencyLevel WEAK = ConsistencyLevel.Weak$.MODULE$;
	@Local ConsistencyLevel CAUSAL = ConsistencyLevel.Causal$.MODULE$;

}
