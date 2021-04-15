package de.tuda.stg.consys.demo.eshop;

import de.tuda.stg.consys.core.legacy.ConsistencyLabel;

/**
 * Created on 19.11.19.
 *
 * @author Mirko Köhler
 */
public class EShopLevels {

	private static ConsistencyLabel weakLevel = null;
	private static ConsistencyLabel strongLevel = null;
	private static ConsistencyLabel causalLevel = null;

	static void setWeak(ConsistencyLabel level) {
		weakLevel = level;
	}

	static void setStrong(ConsistencyLabel level) {
		strongLevel = level;
	}

	static void setCausal(ConsistencyLabel level) {
		causalLevel = level;
	}

	public static ConsistencyLabel getWeakLevel() {
		if (weakLevel == null) throw new IllegalStateException("weak level has not been set yet");
		return weakLevel;
	}

	public static ConsistencyLabel getStrongLevel() {
		if (strongLevel == null) throw new IllegalStateException("strong level has not been set yet");
		return strongLevel;
	}

	public static ConsistencyLabel getCausalLevel() {
		if (causalLevel == null) throw new IllegalStateException("weak level has not been set yet");
		return causalLevel;
	}

}
