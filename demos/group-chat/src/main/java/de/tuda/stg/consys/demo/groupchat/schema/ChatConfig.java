package de.tuda.stg.consys.demo.groupchat.schema;

import de.tuda.stg.consys.checker.qual.ThisConsistent;

public class ChatConfig {
    public int capacity;

    public ChatConfig(@ThisConsistent int capacity) {
        this.capacity = capacity;
    }
}
