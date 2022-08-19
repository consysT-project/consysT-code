//package de.tuda.stg.consys.invariants.crdts.data;
//
//import com.google.common.collect.ImmutableMap;
//import scala.Function0;
//import scala.collection.JavaConverters;
//import scala.collection.Map$;
//import scala.collection.convert.AsJavaConverters;
//
//import java.util.Collection;
//import java.util.Map;
//import java.util.Set;
//
//public class ConsysMap<K, V> implements Map<K, V> {
//
//	private final scala.collection.Map<Object, V> underlying = null;
//
//	public ConsysMap() {
////		underlying = Map$.MODULE$.<Object, V>empty();
//	}
//
//	@Override
//	public int size() {
////		return underlying.size();
//	}
//
//	@Override
//	public boolean isEmpty() {
//		return underlying.isEmpty();
//	}
//
//	@Override
//	public boolean containsKey(Object key) {
//		return underlying.contains(key);
//	}
//
//
//	@Override
//	public boolean containsValue(Object value) {
//		return underlying.find(t -> t._2().equals(value)).isDefined();
//	}
//
//	@Override
//	public V get(Object key) {
//		return underlying.get(key).getOrElse(() -> null);
//	}
//
//	@Override
//	@Deprecated
//	public V put(K key, V value) {
//		throw new UnsupportedOperationException("put is not supported for immutable maps");
//	}
//
//	@Override
//	@Deprecated
//	public V remove(Object key) {
//		throw new UnsupportedOperationException("remove is not supported for immutable maps");
//	}
//
//	@Override
//	@Deprecated
//	public void putAll(Map<? extends K, ? extends V> m) {
//		throw new UnsupportedOperationException("putAll is not supported for immutable maps");
//	}
//
//	@Override
//	@Deprecated
//	public void clear() {
//		throw new UnsupportedOperationException("clear is not supported for immutable maps");
//	}
//
//	@Override
//	public Set<K> keySet() {
//		throw new UnsupportedOperationException("keySet is not supported for immutable maps");
//	}
//
//	@Override
//	public Collection<V> values() {
//		return JavaConverters.<V>asJavaCollection(underlying.values());
//	}
//
//	@Override
//	public Set<Entry<K, V>> entrySet() {
//		throw new UnsupportedOperationException("entrySet is not supported for immutable maps");
//	}
//}
