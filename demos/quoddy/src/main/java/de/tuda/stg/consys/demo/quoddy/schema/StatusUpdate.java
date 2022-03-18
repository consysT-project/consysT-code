package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.japi.Ref;

import java.util.UUID;


public class StatusUpdate extends Post {
    private final String text;

    public StatusUpdate(UUID id, Ref<User> owner, String text) {
        super(id, owner);
        this.text = text;
    }

    public String getText() {
        return text;
    }
}
