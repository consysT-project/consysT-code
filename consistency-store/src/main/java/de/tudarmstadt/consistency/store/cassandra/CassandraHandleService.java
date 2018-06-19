package de.tudarmstadt.consistency.store.cassandra;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.HandleService;
import de.tudarmstadt.consistency.store.StateEvent;

import java.util.Objects;
import java.util.UUID;

/**
 * Created on 19.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraHandleService implements HandleService<UUID, StateEvent> {

	private final CassandraDatabase cassandraDatabase;

	CassandraHandleService(CassandraDatabase cassandraDatabase) {
		this.cassandraDatabase = cassandraDatabase;
	}

	@Override
	@SuppressWarnings("consistency")
	public <T> CassandraHandle<T> obtain(UUID id, Class<? extends T> valueClass, Class<?> consistencyLevel) {

		if (Objects.equals(consistencyLevel, Weak.class)) {
			return new CassandraHandle.WeakHandle<T>(id, cassandraDatabase);
		} else if (Objects.equals(consistencyLevel, Strong.class)) {
			return new CassandraHandle.StrongHandle<T>(id, cassandraDatabase);
		}

		throw new IllegalArgumentException("unknown consistency level");
	}
}
