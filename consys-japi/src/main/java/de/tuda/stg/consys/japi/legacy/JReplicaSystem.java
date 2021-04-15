package de.tuda.stg.consys.japi.legacy;

import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.core.legacy.ConsistencyLabel;


/**
 * Interface for working with replica systems. Replica systems allow users to
 * create new replicated objects or lookup and editing existing replicated
 * objects.
 *
 * @author Mirko Köhler
 */
public interface JReplicaSystem extends AutoCloseable {

	/**
	 * The number of replicas that each object has.
	 */
	int numOfReplicas();

	/**
	 * The number of replicated objects that are stored in this replica system.
	 */
	int numberOfObjects();

	/**
	 * Returns the default timeout in milliseconds. The default timeout is used whenever there is
	 * remote communication.
	 */
	long timeoutInMillis();

	/**
	 * Creates a new replicated object from the given local Java object. The implementation can decide whether the state of
	 * the Java object is copied or retained. In either case, the local object should not be used any further, but
	 * instead method calls and field accesses should be performed on the replicated object.
	 *
	 * @param addr The address of the replicated object, so that it can be referenced on other hosts.
	 * @param obj The state of the replicated object under which it is intialized.
	 * @param consistencyLevel The consistency level of the object. The replica system has to support the given
	 *                            consistency level.
	 * @param <T> The class of the replicated object.
	 * @return A reference to the replicated object.
	 *
	 * @see JRef
	 */
	<T> @Local JRef<T> replicate(String addr, @Local T obj, ConsistencyLabel consistencyLevel);

	/**
	 * Creates a new replicated object from the given local Java object. The implementation can decide whether the state of
	 * the Java object is copied or retained. In either case, the local object should not be used any further, but
	 * instead method calls and field accesses should be performed on the replicated object.
	 * The address of this object is not known.
	 *
	 * @param obj The state of the replicated object under which it is intialized.
	 * @param consistencyLevel The consistency level of the object. The replica system has to support the given
	 *                            consistency level.
	 * @param <T> The type of the replicated object.
	 * @return A reference to the replicated object.
	 *
	 * @see JRef
	 */
	<T> @Local JRef<T> replicate(@Local T obj, ConsistencyLabel consistencyLevel);

	/**
	 * Looks up an existing replicated object by its address. The class of the object has to be known
	 * prior to the lookup.
	 * If the replicated object is not available then the method will wait until it is available (or timeout).
	 *
	 * @param addr The address of the object.
	 * @param objCls The class of the object.
	 * @param consistencyLevel The consistency level of the object. This has to be the same consistency as
	 *                         has been used to replicate the object.
	 * @param <T> The type of the replicated object.
	 * @return A reference to the replicated object.
	 */
	<T> @Local JRef<T> lookup(String addr, Class<T> objCls, ConsistencyLabel consistencyLevel);
}

