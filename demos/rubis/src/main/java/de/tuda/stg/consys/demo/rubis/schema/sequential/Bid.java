package de.tuda.stg.consys.demo.rubis.schema.sequential;

import java.util.Date;
import java.util.UUID;

@SuppressWarnings({"consistency"})
public class Bid {
    private final UUID id;
    private final Date date;
    private final float bid;
    private final User user;

    public Bid(UUID id, float bid, User user) {
        this.id = id;
        this.bid = bid;
        this.user = user;
        this.date = new Date();
    }

    public UUID getId() {
        return id;
    }

    public Date getDate() {
        return date;
    }

    public User getUser() {
        return user;
    }

    public float getBid() {
        return bid;
    }
}
