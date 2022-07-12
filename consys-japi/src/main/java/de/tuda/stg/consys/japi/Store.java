package de.tuda.stg.consys.japi;

import scala.Option;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public interface Store<Addr, Obj, Consistency, TxContext extends TransactionContext<Addr, Obj, Consistency>> {

	<U> Option<U> transaction(Transaction<TxContext, U, Addr, Obj, Consistency> tx);

	void close() throws Exception;
}
