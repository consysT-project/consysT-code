package de.tuda.stg.consys.japi;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public interface TransactionContext<Addr, Obj, Consistency> {

	<T extends Obj> Ref<T> replicate(Addr addr, Consistency level, Class<T> clazz, Object... constructorArgs);

	<T extends Obj> Ref<T> lookup(Addr addr, Consistency level, Class<T> clazz);

}
