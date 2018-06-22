package de.tudarmstadt.consistency.store.cassandra;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.TransactionContext;

import java.lang.annotation.Annotation;
import java.util.Objects;
import java.util.UUID;

/**
 * Created on 19.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraTransactionContext implements TransactionContext<UUID> {

	private final CassandraDatabase cassandraDatabase;

	CassandraTransactionContext(CassandraDatabase cassandraDatabase) {
		this.cassandraDatabase = cassandraDatabase;
	}


	@Override
	public <T> CassandraRef<T> obtain(UUID id, Class<? super T> valueClass, Class<? extends Annotation> consistencyLevel) {
		if (Objects.equals(consistencyLevel, Weak.class)) {
			return new CassandraRef.WeakRef<T>(id, cassandraDatabase);
		} else if (Objects.equals(consistencyLevel, Strong.class)) {
			return new CassandraRef.StrongRef<T>(id, cassandraDatabase);
		}

		throw new IllegalArgumentException("unknown consistency level");
	}
}
