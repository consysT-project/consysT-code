package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public class Bid implements Serializable {
    private final UUID id;
    private final Date date;
    private final float bid;
    private float maxBid;
    private final Ref<User> user;

    public Bid(UUID id, float bid, Ref<User> user, float maxBid) {
        this.id = id;
        this.bid = bid;
        this.user = user;
        this.maxBid = maxBid;
        this.date = new Date();
    }

    public Ref<User> getUser() {
        return user;
    }

    public float getBid() {
        return bid;
    }
}
