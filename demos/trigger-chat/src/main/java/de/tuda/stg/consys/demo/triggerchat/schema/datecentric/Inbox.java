package de.tuda.stg.consys.demo.triggerchat.schema.datecentric;

import de.tuda.stg.consys.checker.qual.Mixed;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

public class Inbox implements Serializable {
    private final List<String> entries = new LinkedList<>();

    public void send(String msg) {
        entries.add(msg);
    }
}
