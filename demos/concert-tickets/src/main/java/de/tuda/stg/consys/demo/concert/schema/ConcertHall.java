package de.tuda.stg.consys.demo.concert.schema;

import java.io.Serializable;

public class ConcertHall implements Serializable {
    public Integer maxAudience;

    public ConcertHall(int maxAudience) {
        this.maxAudience = maxAudience;
    }
}
