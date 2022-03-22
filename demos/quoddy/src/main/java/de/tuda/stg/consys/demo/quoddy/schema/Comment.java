package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;

public class Comment implements Serializable {
    private final String text;
    private final Ref<User> owner;
    private final Date timestamp;

    public Comment(String text, Ref<User> owner, Date timestamp) {
        this.text = text;
        this.owner = owner;
        this.timestamp = timestamp;
    }

    public String getText() {
        return text;
    }

    public Ref<User> getOwner() {
        return owner;
    }

    public Date getTimestamp() {
        return timestamp;
    }
}
