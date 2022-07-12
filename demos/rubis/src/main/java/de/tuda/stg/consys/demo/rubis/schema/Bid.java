package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public @Strong class Bid implements Serializable {
    private final @Immutable UUID id;
    private final @Immutable Date date;
    private final @Immutable float bid;
    private final @Immutable Ref<? extends @Mutable IUser> user;

    public Bid(@Immutable @Local UUID id, @Immutable @Local float bid, Ref<? extends @Mutable IUser> user) {
        this.id = id;
        this.bid = bid;
        this.user = user;
        this.date = new Date();
    }

    @SideEffectFree
    public @Strong UUID getId() {
        return id;
    }

    @SideEffectFree
    public @Strong Date getDate() {
        return date;
    }

    @SideEffectFree
    public Ref<? extends @Mutable IUser> getUser() {
        return user;
    }

    @SideEffectFree
    public @Strong float getBid() {
        return bid;
    }
}
