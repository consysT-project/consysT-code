package de.tuda.stg.consys.demo.eshop;

import de.tuda.stg.consys.objects.ConsistencyLevel;

/**
 * Created on 19.11.19.
 *
 * @author Mirko Köhler
 */
public class EShopLevels {

	private static ConsistencyLevel weakLevel = null;
	private static ConsistencyLevel strongLevel = null;
	private static ConsistencyLevel causalLevel = null;

	static void setWeak(ConsistencyLevel level) {
		weakLevel = level;
	}

	static void setStrong(ConsistencyLevel level) {
		strongLevel = level;
	}

	static void setCausal(ConsistencyLevel level) {
		causalLevel = level;
	}

	public static ConsistencyLevel getWeakLevel() {
		if (weakLevel == null) throw new IllegalStateException("weak level has not been set yet");
		return weakLevel;
	}

	public static ConsistencyLevel getStrongLevel() {
		if (strongLevel == null) throw new IllegalStateException("strong level has not been set yet");
		return strongLevel;
	}

	public static ConsistencyLevel getCausalLevel() {
		if (causalLevel == null) throw new IllegalStateException("weak level has not been set yet");
		return causalLevel;
	}

}
