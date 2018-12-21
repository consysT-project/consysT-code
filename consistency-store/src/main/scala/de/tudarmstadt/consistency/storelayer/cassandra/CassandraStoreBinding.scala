package de.tudarmstadt.consistency.storelayer.cassandra

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
trait CassandraStoreBinding[Id, Key, Data, TxStatus, Isolation, Consistency]
	extends SessionBinding[Id, Key, Data, TxStatus, Isolation, Consistency]
	with DataBinding[Id, Key, Data, TxStatus, Isolation, Consistency]
	with OptimisticLocksBinding[Id, Key]
	with TransactionCoordinationBinding[Id, TxStatus, Isolation]
	with TxStatusBindings[TxStatus]