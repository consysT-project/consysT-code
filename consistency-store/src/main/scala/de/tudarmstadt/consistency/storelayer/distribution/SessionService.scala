package de.tudarmstadt.consistency.storelayer.distribution

import com.datastax.driver.core.Cluster
import de.tudarmstadt.consistency.storelayer.distribution.cassandra.CassandraTypeBinding

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait SessionService[Id, Key, Data, TxStatus, Isolation, Consistency] {

	/* class definitions */

	/* references to other database entries */
	case class OpRef(id : Id, key : Key) {
		assert(id != null)
		assert(key != null)
		def toTuple : (Id, Key) =	(id, key)
	}
	case class TxRef(id : Id) {
		assert(id != null)
	}

}
