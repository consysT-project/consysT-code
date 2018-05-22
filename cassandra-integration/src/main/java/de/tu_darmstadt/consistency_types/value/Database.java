package de.tu_darmstadt.consistency_types.value;

import java.io.Serializable;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
public interface Database<Key> extends AutoCloseable {

	void initialize();
	DatabaseConnector<Key>[] connectors();

	interface DatabaseConnector<ConnectorKey> {
	//	<V extends Serializable> DatabaseValue<V> obtainValue(ConnectorKey id);
	}
}

