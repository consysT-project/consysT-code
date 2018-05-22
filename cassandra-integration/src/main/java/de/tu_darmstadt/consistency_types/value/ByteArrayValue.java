package de.tu_darmstadt.consistency_types.value;

import java.io.*;

/**
 * Created on 22.05.18.
 *
 * @author Mirko Köhler
 */
public abstract class ByteArrayValue<V extends Serializable> implements DatabaseValue<V> {

	@Override
	public V read() throws IOException, ClassNotFoundException {

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
	public void write(V value) throws IOException {

		ByteArrayOutputStream bos = new ByteArrayOutputStream();
		ObjectOutputStream oos = new ObjectOutputStream(bos);

		//Transform object into a string representation
		oos.writeObject(value);
		byte[] data = bos.toByteArray();

		writeBytes(data);
	}

	protected abstract void writeBytes(byte[] bytes);
}
