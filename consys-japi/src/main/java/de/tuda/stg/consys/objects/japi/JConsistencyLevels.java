package de.tuda.stg.consys.objects.japi;

import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.objects.ConsistencyLevel;

/**
 * Created on 14.03.19.
 *
 * @author Mirko Köhler
 */
public interface JConsistencyLevels {

	@Local ConsistencyLevel STRONG = ConsistencyLevel.Strong$.MODULE$;
	@Local ConsistencyLevel WEAK = ConsistencyLevel.Weak$.MODULE$;


}
