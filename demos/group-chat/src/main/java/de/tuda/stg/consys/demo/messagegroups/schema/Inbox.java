package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.common.returnsreceiver.qual.This;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;


public class Inbox implements Serializable {
    private final List<@Weak String> messages = new LinkedList<>();

    @Transactional
    public void postMessage(Ref<@Weak User> user, @Weak String message) {
        messages.add(user.ref().name + ": " + message);
    }
}
