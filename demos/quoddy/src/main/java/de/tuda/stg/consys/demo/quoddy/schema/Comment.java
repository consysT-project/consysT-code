package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Date;

public class Comment implements Serializable {
    private final @Immutable String text;
    private final @Immutable Ref<User> owner;
    private final @Immutable Date timestamp;

    public Comment(@Weak @Immutable String text, Ref<User> owner, @Weak @Immutable Date timestamp) {
        this.text = text;
        this.owner = owner;
        this.timestamp = timestamp;
    }

    @SideEffectFree
    public String getText() {
        return text;
    }

    @SideEffectFree
    public Ref<User> getOwner() {
        return owner;
    }

    @SideEffectFree
    public Date getTimestamp() {
        return timestamp;
    }
}
