package de.tudarmstadt.consistency.store.cassandra;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Ref;
import de.tudarmstadt.consistency.store.ReferenceService;

import java.lang.annotation.Annotation;
import java.util.Objects;
import java.util.UUID;

/**
 * Created on 19.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraReferenceService implements ReferenceService<UUID> {

	private final CassandraDatabase cassandraDatabase;

	CassandraReferenceService(CassandraDatabase cassandraDatabase) {
		this.cassandraDatabase = cassandraDatabase;
	}


	@Override
	public <T, R extends Ref<T, R>> R obtain(UUID id, Class<? extends T> valueClass, Class<? extends Annotation> consistencyLevel) {
		if (Objects.equals(consistencyLevel, Weak.class)) {
			return (R) new CassandraRef.WeakRef<T>(id, cassandraDatabase);
		} else if (Objects.equals(consistencyLevel, Strong.class)) {
			return (R) new CassandraRef.StrongRef<T>(id, cassandraDatabase);
		}

		throw new IllegalArgumentException("unknown consistency level");
	}
}
