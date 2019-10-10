package de.tuda.stg.consys.messagegroups;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class Address {

	private final String hostname;
	private final int port;

	public Address(String hostname, int port) {
		this.hostname = hostname;
		this.port = port;
	}

	public Address(String hostnameAndPort) {
		String[] splitted = hostnameAndPort.split(":", 2);
		this.hostname = splitted[0];
		this.port = Integer.parseInt(splitted[1]);
	}

	@Override
	public boolean equals(Object obj) {
		return obj instanceof Address && ((Address) obj).hostname.equals(hostname) && ((Address) obj).port == port;
	}

	@Override
	public int hashCode() {
		return hostname.hashCode() << 6 & port;
	}

	public int getPort() {
		return port;
	}

	public String getHostname() {
		return hostname;
	}

	@Override
	public String toString() {
		return hostname + ":" + port;
	}
}
