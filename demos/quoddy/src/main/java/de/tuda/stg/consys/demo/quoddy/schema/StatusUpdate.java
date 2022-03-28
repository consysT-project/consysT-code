package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

import java.util.UUID;


public @Mixed class StatusUpdate extends Post {
    private String text;

    public StatusUpdate(@Local @Immutable UUID id, Ref<User> owner, @Weak @Mutable String text) {
        super(id, owner);
        this.text = text;
    }

    public void setText(@Weak @Mutable String text) {
        this.text = text;
    }

    public String getText() {
        return text;
    }

    @Override
    public String toString() {
        return "Posted by " + getOwner() + " on " + getCreationTimestamp() + ": " + getText();
    }
}
