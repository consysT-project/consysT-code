package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.UUID;

public @Mixed class Event extends Post {
    private Date date;
    private @Weak String text;
    private final List<Ref<User>> subscribers;
    private Ref<Event> self; // not ideal, as it must be set after creation

    public Event(@Local @Immutable UUID id, Ref<User> owner, @Strong @Mutable Date date, @Weak @Mutable String text) {
        super(id, owner);
        this.date = date;
        this.text = text;
        this.subscribers = new LinkedList<>();
    }

    public void initSelf(Ref<Event> self) {
        this.self = self;
    }

    public void addSubscriber(Ref<User> user) {
        this.subscribers.add(user);
    }

    @Transactional
    @StrongOp
    public void postUpdate(@Weak @Mutable String text) {
        this.text += "Update (" + new Date() + "): " + text;
        for (@Mixed Ref<User> user : subscribers) {
            user.ref().notifyOfEventUpdate(self);
        }
    }

    @Transactional
    @StrongOp
    public void postUpdate(@Weak @Mutable String text, @Strong @Mutable Date newDate) {
        this.text += "Update (" + new Date() + "): " + text;
        this.date = newDate;
        for (@Mixed Ref<User> user : subscribers) {
            user.ref().notifyOfEventUpdate(self);
        }
    }
}
