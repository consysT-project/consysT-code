package de.tuda.stg.consys.triggerchat.schema.opcentric;

import de.tuda.stg.consys.checker.qual.Mixed;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

public @Mixed class Inbox implements Serializable {
    private final List<String> entries = new LinkedList<>();

    public void send(String msg) {
        entries.add(msg);
    }
}
