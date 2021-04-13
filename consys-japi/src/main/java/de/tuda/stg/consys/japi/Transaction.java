package de.tuda.stg.consys.japi;

import scala.Option;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
@FunctionalInterface
public interface Transaction<Context extends TransactionContext<Addr, Obj, Consistency>, U, Addr, Obj, Consistency> {
	Option<U> doTransaction(Context context);
}
