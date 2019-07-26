package objects.japi;

import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.objects.ConsistencyLevel;

/**
 * Created on 14.03.19.
 *
 * @author Mirko Köhler
 */
public class JConsistencyLevel {

	public static final @Local ConsistencyLevel STRONG = ConsistencyLevel.Strong$.MODULE$;
	public static final @Local ConsistencyLevel WEAK = ConsistencyLevel.Weak$.MODULE$;


}
