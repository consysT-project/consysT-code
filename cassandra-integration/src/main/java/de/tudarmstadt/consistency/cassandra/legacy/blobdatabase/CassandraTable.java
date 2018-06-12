package de.tudarmstadt.consistency.cassandra.legacy.blobdatabase;

/**
 * Created on 28.05.18.
 *
 * @author Mirko Köhler
 */
public interface CassandraTable {
	String getTableName();

	void initialize();
}
