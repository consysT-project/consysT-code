package de.tuda.stg.consys.demo.rubis.schema;

import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public @Mixed class Bid implements Serializable {
    private final @Immutable UUID id;
    private final @Immutable Date date;
    private final @Immutable float bid;
    private final @Immutable Ref<@Mutable User> user;

    public Bid(@Immutable @Local UUID id, @Immutable @Local float bid, Ref<@Mutable User> user) {
        this.id = id;
        this.bid = bid;
        this.user = user;
        this.date = new Date();
    }

    @WeakOp
    @SideEffectFree
    public @Strong UUID getId() {
        return id;
    }

    @WeakOp
    @SideEffectFree
    public @Strong Date getDate() {
        return date;
    }

    @WeakOp
    @SideEffectFree
    public Ref<@Mutable User> getUser() {
        return user;
    }

    @WeakOp
    @SideEffectFree
    public @Strong float getBid() {
        return bid;
    }
}