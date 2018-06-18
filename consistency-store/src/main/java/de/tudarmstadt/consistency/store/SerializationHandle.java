package de.tudarmstadt.consistency.store;

import de.tudarmstadt.consistency.store.Handle;

import java.io.*;

/**
 * Handler for databases that store serialized objects.
 *
 * @author Mirko Köhler
 */
public abstract class SerializationHandle<V> extends ReadWriteHandle<V> {

	@Override
	@SuppressWarnings("unchecked")
	protected V handleRead() throws Exception {

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
	protected void handleWrite(V value) throws Exception {

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
