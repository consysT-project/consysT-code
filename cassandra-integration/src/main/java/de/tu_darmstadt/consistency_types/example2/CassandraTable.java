package de.tu_darmstadt.consistency_types.example2;

/**
 * Created on 28.05.18.
 *
 * @author Mirko Köhler
 */
public interface CassandraTable {
	String getTableName();

	void initialize();
}
