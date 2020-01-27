package de.tuda.stg.consys.japi.impl.cassandra;

import scala.Option;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public interface Replica<Addr, Obj, Consistency, TxContext extends TransactionContext<Addr, Obj, Consistency>> {

	<U> Option<U> transaction(Transaction<TxContext, U, Addr, Obj, Consistency> tx);

	void close() throws Exception;
}
