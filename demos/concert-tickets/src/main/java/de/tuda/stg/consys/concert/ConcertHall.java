package de.tuda.stg.consys.concert;

import java.io.Serializable;

public class ConcertHall implements Serializable {
    public int maxAudience;

    public ConcertHall(int maxAudience) {
        this.maxAudience = maxAudience;
    }
}
