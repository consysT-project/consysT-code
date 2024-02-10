package de.tuda.stg.consys.demo.groupchat.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;


public class Inbox implements Serializable {
    private final List<@Weak String> messages = new LinkedList<>();

    @Transactional
    public void postMessage(Ref<@Weak User> user, @Weak String message) {
        messages.add(user.ref().name + ": " + message);
    }
}
