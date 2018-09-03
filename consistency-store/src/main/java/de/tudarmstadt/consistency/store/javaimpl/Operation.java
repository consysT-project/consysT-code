package de.tudarmstadt.consistency.store.javaimpl;


/**
 * Created on 20.06.18.
 *
 * @author Mirko Köhler
 */
@FunctionalInterface
public interface Operation<T, R extends Ref<T, R>, Param, Return> {

	Return compute(R ref, Param additionalParameter) throws Exception;
}
