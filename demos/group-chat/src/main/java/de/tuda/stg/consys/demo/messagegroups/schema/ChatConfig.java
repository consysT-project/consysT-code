package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.checker.qual.ThisConsistent;

public class ChatConfig {
    public int capacity;

    public ChatConfig(@ThisConsistent int capacity) {
        this.capacity = capacity;
    }
}
