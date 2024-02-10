package de.tuda.stg.consys.demo.rubis.schema.opcentric;

import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public @Strong class Bid implements Serializable {
    private final @Immutable UUID id;
    private final @Immutable Date date;
    private final @Immutable float bid;
    private final @Immutable Ref<@Mutable User> user;

    public Bid(@Immutable @Local UUID id, @Local float bid, Ref<@Mutable User> user) {
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
    public Ref<@Mutable User> getUser() {
        return user;
    }

    @SideEffectFree
    public @Strong float getBid() {
        return bid;
    }
}
