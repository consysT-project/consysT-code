package de.tudarmstadt.consistency.storelayer.distribution

import com.datastax.driver.core.Cluster
import de.tudarmstadt.consistency.storelayer.distribution.cassandra.CassandraTypeBinding

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait SessionService[Id, Txid, Key, Data, TxStatus, Isolation, Consistency] {

	/* class definitions */
	type OpRef = de.tudarmstadt.consistency.storelayer.distribution.OpRef[Id, Key]
	type TxRef = de.tudarmstadt.consistency.storelayer.distribution.TxRef[Txid]

	//For communication with the outside world.


}
