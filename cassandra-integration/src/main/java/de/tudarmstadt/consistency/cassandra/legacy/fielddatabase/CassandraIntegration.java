package de.tudarmstadt.consistency.cassandra.legacy.fielddatabase;

import com.google.common.collect.Maps;

import java.util.Map;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraIntegration {

	private final Map<Class<?>, CassandraTable> tables;

	public CassandraIntegration() {
		tables = Maps.newHashMap();
	}
}
