package de.tu_darmstadt.consistency_types.store.impl;

import de.tu_darmstadt.consistency_types.store.Handle;

import java.io.*;

/**
 * Created on 22.05.18.
 *
 * @author Mirko Köhler
 */
public abstract class SerializerHandle<V> implements Handle<V> {

	@Override
	@SuppressWarnings("unchecked")
	public V get() throws IOException, ClassNotFoundException {

		byte[] data = readBytes();

		if (data == null) {
			return null;
		}

		ByteArrayInputStream bis = new ByteArrayInputStream(data);
		ObjectInputStream ois = new ObjectInputStream(bis);

		Object o = ois.readObject();

		return (V) o;
	}

	/**
	 * Retrieves the bytes associated with this database value from the
	 * database.
	 *
	 * @return A byte array consisting of the serialized object, or null
	 * if the value could not been read.
	 */
	protected abstract byte[] readBytes();

	@Override
	public void set(V value) throws IOException {

		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		ObjectOutputStream oos = new ObjectOutputStream(bos);

		//Transform object into a string representation
		oos.writeObject(value);
		oos.flush();

		byte[] data = bos.toByteArray();

		writeBytes(data);
	}

	protected abstract void writeBytes(byte[] bytes);
}
