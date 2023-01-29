package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.checker.qual.Mixed;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;


public @Mixed class Inbox implements Serializable {
    private final List<String> entries = new LinkedList<>();

    public void add(String msg) {
        entries.add(msg);
    }

    @SideEffectFree
    public List<String> getEntries() {
        return entries;
    }

    @Override
    @SideEffectFree
    public String toString() {
        return entries.toString();
    }
}
