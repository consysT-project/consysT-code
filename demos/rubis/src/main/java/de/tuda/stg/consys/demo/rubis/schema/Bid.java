package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public class Bid implements Serializable {
    private final UUID id;
    private final Date date;
    private final float bid;
    private final Ref<User> user;

    public Bid(UUID id, float bid, Ref<User> user) {
        this.id = id;
        this.bid = bid;
        this.user = user;
        this.date = new Date();
    }

    @WeakOp
    public UUID getId() {
        return id;
    }

    @WeakOp
    public Date getDate() {
        return date;
    }

    @WeakOp
    public Ref<User> getUser() {
        return user;
    }

    @WeakOp
    public float getBid() {
        return bid;
    }
}
