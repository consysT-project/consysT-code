package de.tudarmstadt.consistency.storelayer.distribution.cassandra

import com.datastax.driver.core.TypeCodec

/**
	* Created on 21.12.18.
	*
	* @author Mirko Köhler
	*/
class CassandraTypeBinding[Id : TypeCodec, Txid : TypeCodec, Key : TypeCodec, Data : TypeCodec, TxStatus : TypeCodec, Isolation : TypeCodec, Consistency : TypeCodec] {

	object TypeCodecs {
		def Id : TypeCodec[Id] = implicitly[TypeCodec[Id]]
		def Txid : TypeCodec[Txid] = implicitly[TypeCodec[Txid]]
		def Key : TypeCodec[Key] = implicitly[TypeCodec[Key]]
		def Data : TypeCodec[Data] = implicitly[TypeCodec[Data]]
		def TxStatus : TypeCodec[TxStatus] = implicitly[TypeCodec[TxStatus]]
		def Isolation : TypeCodec[Isolation] = implicitly[TypeCodec[Isolation]]
		def Consistency : TypeCodec[Consistency] = implicitly[TypeCodec[Consistency]]
	}

}
