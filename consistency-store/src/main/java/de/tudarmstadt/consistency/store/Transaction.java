package de.tudarmstadt.consistency.store;

/**
 * Created on 19.06.18.
 *
 * @author Mirko Köhler
 */
@FunctionalInterface
public interface Transaction<Service extends HandleService> {

	void executeWith(Service service) throws Exception;

}
