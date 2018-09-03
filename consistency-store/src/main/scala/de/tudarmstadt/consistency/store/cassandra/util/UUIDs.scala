package de.tudarmstadt.consistency.store.cassandra.util

/**
	* This code has been adapted from com.datastax.driver.core.utils.UUIDs.
	*
	* Changes are that it is now possible to generate UUIDs from a given timestamp and that type 1 UUIDs (timebased)
	* now have another random portion in them.
	*
	* @author Mirko Köhler
	*/
/*
 * Copyright DataStax, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import java.lang.management.ManagementFactory
import java.net.{InetAddress, NetworkInterface, SocketException, UnknownHostException}
import java.security.{MessageDigest, NoSuchAlgorithmException}
import java.util._
import java.util.concurrent.atomic.AtomicLong

import com.datastax.driver.core.Native
import com.google.common.base.Charsets

import scala.collection.mutable


/**
	* Utility methods to help working with UUIDs, and more specifically, with time-based UUIDs
	* (also known as Version 1 UUIDs).
	* <h3>Notes on the algorithm used to generate time-based UUIDs</h3>
	* The algorithm follows roughly the description in RFC-4122, but with the following adaptations:
	* <ol>
	* <li>Since Java does not provide direct access to the host's MAC address, that information
	* is replaced with a digest of all IP addresses available on the host;</li>
	* <li>The process ID (PID) isn't easily available to Java either, so it is determined by one of the
	* following methods, in the order they are listed below:
	* <ol>
	* <li>If the System  property <code>{@value PID_SYSTEM_PROPERTY}</code> is set then the value to use as a PID
	* will be read from that property;</li>
	* <li>Otherwise, if a native call to {@link Native#processId() getpid()} is possible, then the PID
	* will be read from that call;</li>
	* <li>Otherwise, an attempt will be made to read the PID from JMX's
	* {@link ManagementFactory#getRuntimeMXBean() RuntimeMXBean}, which is a well-known,
	* yet undocumented "hack", since most JVMs tend to use the JVM's PID as part of that MXBean name;</li>
	* <li>If all of the above fails, a random integer will be generated and used as a surrogate PID.</li>
	* </ol>
	* </li>
	* </ol>
	*
	* @see <a href="https://datastax-oss.atlassian.net/browse/JAVA-444">JAVA-444</a>
	* @see <a href="http://www.ietf.org/rfc/rfc4122.txt">A Universally Unique IDentifier (UUID) URN Namespace (RFC 4122)</a>
	*/
object UUIDs {
	/**
		* The System property to use to force the value of the process ID (PID).
		*/
	val PID_SYSTEM_PROPERTY = "com.datastax.driver.PID"

	private val START_EPOCH = makeEpoch
	private val CLOCK_SEQ_AND_NODE = makeClockSeqAndNode



	/*
	 * The min and max possible lsb for a UUID.
	 * Note that his is not 0 and all 1's because Cassandra TimeUUIDType
	 * compares the lsb parts as a signed byte array comparison. So the min
	 * value is 8 times -128 and the max is 8 times +127.
	 *
	 * Note that we ignore the uuid variant (namely, MIN_CLOCK_SEQ_AND_NODE
	 * have variant 2 as it should, but MAX_CLOCK_SEQ_AND_NODE have variant 0)
	 * because I don't trust all uuid implementation to have correctly set
	 * those (pycassa don't always for instance).
	 */
	private val MIN_CLOCK_SEQ_AND_NODE = 0x8080808080808080L
	private val MAX_CLOCK_SEQ_AND_NODE = 0x7f7f7f7f7f7f7f7fL

	private val lastTimestamp = new AtomicLong(0L)

	private def makeEpoch = { // UUID v1 timestamp must be in 100-nanoseconds interval since 00:00:00.000 15 Oct 1582.
		val c = Calendar.getInstance(TimeZone.getTimeZone("GMT-0"))
		c.set(Calendar.YEAR, 1582)
		c.set(Calendar.MONTH, Calendar.OCTOBER)
		c.set(Calendar.DAY_OF_MONTH, 15)
		c.set(Calendar.HOUR_OF_DAY, 0)
		c.set(Calendar.MINUTE, 0)
		c.set(Calendar.SECOND, 0)
		c.set(Calendar.MILLISECOND, 0)
		c.getTimeInMillis
	}

	private def makeNode : Long = {
		/*
						* We don't have access to the MAC address (in pure JAVA at least) but
						* need to generate a node part that identify this host as uniquely as
						* possible.
						* The spec says that one option is to take as many source that
						* identify this node as possible and hash them together. That's what
						* we do here by gathering all the ip of this host as well as a few
						* other sources.
						*/ try {
			val digest = MessageDigest.getInstance("MD5")
			for (address <- getAllLocalAddresses) {
				update(digest, address)
			}
			val props = System.getProperties
			update(digest, props.getProperty("java.vendor"))
			update(digest, props.getProperty("java.vendor.url"))
			update(digest, props.getProperty("java.version"))
			update(digest, props.getProperty("os.arch"))
			update(digest, props.getProperty("os.name"))
			update(digest, props.getProperty("os.version"))
			update(digest, getProcessPiece)
			val hash = digest.digest
			var node : Long = 0
			var i = 0
			while (i < 6) {
				node |= (0x00000000000000ffL & hash(i).toLong) << (i * 8)
				i += 1
			}

			// Since we don't use the mac address, the spec says that multicast
			// bit (least significant bit of the first byte of the node ID) must be 1.
			node | 0x0000010000000000L
		} catch {
			case e : NoSuchAlgorithmException =>
				throw new RuntimeException(e)
		}
	}
	private def getProcessPiece = {
		var pid : Integer = null
		val pidProperty = System.getProperty(PID_SYSTEM_PROPERTY)
		if (pidProperty != null) try {
			pid = pidProperty.toInt
		} catch {
			case e : NumberFormatException =>
		}
		if (pid == null && Native.isGetpidAvailable) try {
			pid = Native.processId
			if (pid == 0) {
				pid = null
			}
		} catch {
			case e : Exception =>
		}
		if (pid == null) try {
			val pidJmx = ManagementFactory.getRuntimeMXBean.getName.split("@")(0)
			pid = pidJmx.toInt
		} catch {
			case e : Exception =>
		}
		if (pid == null) {
			pid = new Random().nextInt
		}
		val loader = UUIDs.getClass.getClassLoader
		val loaderId = if (loader != null) System.identityHashCode(loader)
		else 0
		Integer.toHexString(pid) + Integer.toHexString(loaderId)
	}

	private def update(digest : MessageDigest, value : String) : Unit = {
		if (value != null) digest.update(value.getBytes(Charsets.UTF_8))
	}

	private def makeClockSeqAndNode: Long = {
		val clock : Long = new Random(System.currentTimeMillis).nextLong
		val node : Long = makeNode
		var lsb : Long = 0
		lsb |= (clock & 0x0000000000003FFFL) << 48
		lsb |= 0x8000000000000000L
		lsb |= node
		lsb
	}

	/**
		* Creates a new random (version 4) UUID.
		* <p/>
		* This method is just a convenience for {@code UUID.randomUUID()}.
		*
		* @return a newly generated, pseudo random, version 4 UUID.
		*/
	def random : UUID = UUID.randomUUID

	/**
		* Creates a new time-based (version 1) UUID.
		* <p/>
		* UUIDs generated by this method are suitable for use with the
		* {@code timeuuid} Cassandra type. In particular the generated UUID
		* includes the timestamp of its generation.
		* <p/>
		* Note that there is no way to provide your own timestamp. This is deliberate, as we feel that this does not
		* conform to the UUID specification, and therefore don't want to encourage it through the API.
		* If you want to do it anyway, use the following workaround:
		* <pre>
		* Random random = new Random();
		* UUID uuid = new UUID(UUIDs.startOf(userProvidedTimestamp).getMostSignificantBits(), random.nextLong());
		* </pre>
		* If you simply need to perform a range query on a {@code timeuuid} column, use the "fake" UUID generated by
		* {@link #startOf(long)} and {@link #endOf(long)}.
		*
		* @return a new time-based UUID.
		*/
	def timeBased : UUID =
		timeBased(getCurrentTimestamp)

	def timeBased(timestamp : Long) : UUID =
		new UUID(makeMSB(timestamp), CLOCK_SEQ_AND_NODE)

	/**
		* Creates a "fake" time-based UUID that sorts as the smallest possible
		* version 1 UUID generated at the provided timestamp.
		* <p/>
		* Such created UUIDs are useful in queries to select a time range of a
		* {@code timeuuid} column.
		* <p/>
		* The UUIDs created by this method <b>are not unique</b> and as such are
		* <b>not</b> suitable for anything else than querying a specific time
		* range. In particular, you should not insert such UUIDs. "True" UUIDs from
		* user-provided timestamps are not supported (see {@link #timeBased()}
		* for more explanations).
		* <p/>
		* Also, the timestamp to provide as a parameter must be a Unix timestamp (as
		* returned by {@link System#currentTimeMillis} or {@link java.util.Date#getTime}), and
		* <em>not</em> a count of 100-nanosecond intervals since 00:00:00.00, 15 October 1582 (as required by RFC-4122).
		* <p/>
		* In other words, given a UUID {@code uuid}, you should never call
		* {@code startOf(uuid.timestamp())} but rather
		* {@code startOf(unixTimestamp(uuid))}.
		* <p/>
		* Lastly, please note that Cassandra's {@code timeuuid} sorting is not compatible
		* with {@link UUID#compareTo} and hence the UUIDs created by this method
		* are not necessarily lower bound for that latter method.
		*
		* @param timestamp the Unix timestamp for which the created UUID must be a
		*                  lower bound.
		* @return the smallest (for Cassandra { @code timeuuid} sorting) UUID of { @code timestamp}.
		*/
	def startOf(timestamp : Long) = new UUID(makeMSB(fromUnixTimestamp(timestamp)), MIN_CLOCK_SEQ_AND_NODE)

	/**
		* Creates a "fake" time-based UUID that sorts as the biggest possible
		* version 1 UUID generated at the provided timestamp.
		* <p/>
		* See {@link #startOf(long)} for explanations about the intended usage of such UUID.
		*
		* @param timestamp the Unix timestamp for which the created UUID must be an
		*                  upper bound.
		* @return the biggest (for Cassandra { @code timeuuid} sorting) UUID of { @code timestamp}.
		*/
	def endOf(timestamp : Long) : UUID = {
		val uuidTstamp = fromUnixTimestamp(timestamp + 1) - 1

				new UUID(makeMSB(uuidTstamp), MAX_CLOCK_SEQ_AND_NODE)
	}
	/**
		* Return the Unix timestamp contained by the provided time-based UUID.
		* <p/>
		* This method is not equivalent to {@link UUID#timestamp()}. More
		* precisely, a version 1 UUID stores a timestamp that represents the
		* number of 100-nanoseconds intervals since midnight, 15 October 1582 and
		* that is what {@link UUID#timestamp()} returns. This method however
		* converts that timestamp to the equivalent Unix timestamp in
		* milliseconds, i.e. a timestamp representing a number of milliseconds
		* since midnight, January 1, 1970 UTC. In particular, the timestamps
		* returned by this method are comparable to the timestamps returned by
		* {@link System#currentTimeMillis}, {@link java.util.Date#getTime}, etc.
		*
		* @param uuid the UUID to return the timestamp of.
		* @return the Unix timestamp of { @code uuid}.
		* @throws IllegalArgumentException if { @code uuid} is not a version 1 UUID.
		*/
	def unixTimestamp(uuid : UUID) : Long = {
		if (uuid.version != 1)
			throw new IllegalArgumentException(s"Can only retrieve the unix timestamp for version 1 uuid (provided version ${uuid.version})" )
		val timestamp = uuid.timestamp
		(timestamp / 10000) + START_EPOCH
	}


	/*
			 * Note that currently we use {@link System#currentTimeMillis} for a base time in
			 * milliseconds, and then if we are in the same milliseconds that the
			 * previous generation, we increment the number of nanoseconds.
			 * However, since the precision is 100-nanoseconds intervals, we can only
			 * generate 10K UUID within a millisecond safely. If we detect we have
			 * already generated that much UUID within a millisecond (which, while
			 * admittedly unlikely in a real application, is very achievable on even
			 * modest machines), then we stall the generator (busy spin) until the next
			 * millisecond as required by the RFC.
			 */
	/**
		* Returns the current timestamp. Makes sure that there are no two timestamps the same.
		* Can safely generate 10k UUIDs per millisecond.
		*
		* @return A current timestamp that is different from the prvious one.
		*/
	def getCurrentTimestamp : Long = {
		while (true) {
			val now = fromUnixTimestamp(System.currentTimeMillis)

			val last = lastTimestamp.get

			if (now > last) if (lastTimestamp.compareAndSet(last, now)) return now

			else {
				val lastMillis = millisOf(last)
				// If the clock went back in time, bail out
				if (millisOf(now) < millisOf(last))
					return lastTimestamp.incrementAndGet

				val candidate = last + 1
				// If we've generated more than 10k uuid in that millisecond,
				// we restart the whole process until we get to the next millis.
				// Otherwise, we try use our candidate ... unless we've been
				// beaten by another thread in which case we try again.
				if (millisOf(candidate) == lastMillis && lastTimestamp.compareAndSet(last, candidate))
					return candidate
			}
		}

		//This is never returned...
		0L
	}
	// Package visible for testing
	def fromUnixTimestamp(tstamp : Long) = (tstamp - START_EPOCH) * 10000

	private def millisOf(timestamp : Long) = timestamp / 10000

	def makeMSB(timestamp : Long) = {
		var msb = 0L
		msb |= (0x00000000ffffffffL & timestamp) << 32
		msb |= (0x0000ffff00000000L & timestamp) >>> 16
		msb |= (0x0fff000000000000L & timestamp) >>> 48
		msb |= 0x0000000000001000L // sets the version to 1.

		msb
	}
	private def getAllLocalAddresses = {
		val allIps : mutable.Set[String] = mutable.HashSet.empty
		try {
			val localhost = InetAddress.getLocalHost
			allIps.add(localhost.toString)
			// Also return the hostname if available, it won't hurt (this does a dns lookup, it's only done once at startup)
			allIps.add(localhost.getCanonicalHostName)
			val allMyIps : Array[InetAddress] = InetAddress.getAllByName(localhost.getCanonicalHostName)
			if (allMyIps != null) {
				var i = 0
				while (i < allMyIps.length) {
					allIps.add(allMyIps(i).toString)
					i += 1
					i - 1
				}
			}
		} catch {
			case e : UnknownHostException =>

			// Ignore, we'll try the network interfaces anyway
		}
		try {
			val en = NetworkInterface.getNetworkInterfaces
			if (en != null) while ( {
				en.hasMoreElements
			}) {
				val enumIpAddr = en.nextElement.getInetAddresses
				while ( {
					enumIpAddr.hasMoreElements
				}) allIps.add(enumIpAddr.nextElement.toString)
			}
		} catch {
			case e : SocketException =>

			// Ignore, if we've really got nothing so far, we'll throw an exception
		}
		allIps
	}
}
