package de.tuda.stg.consys.japi.next;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public interface TransactionContext<Addr, Obj, Consistency> {

	<T extends Obj> Ref<T> replicate(Addr addr, T object, Consistency level);

	<T extends Obj> Ref<T> lookup(Addr addr, Class<T> clazz, Consistency level);

}
