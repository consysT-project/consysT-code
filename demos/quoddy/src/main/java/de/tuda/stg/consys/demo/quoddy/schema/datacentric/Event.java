package de.tuda.stg.consys.demo.quoddy.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.quoddy.schema.IEvent;
import de.tuda.stg.consys.demo.quoddy.schema.IUser;
import de.tuda.stg.consys.japi.Ref;

import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.UUID;

public @Weak class Event extends Post implements IEvent {
    private final Ref<@Strong @Mutable Date> date;
    private @Weak String text;
    private final List<Ref<? extends @Mutable IUser>> subscribers;
    private Ref<? extends IEvent> self; // not ideal, as it must be set after creation

    public Event(@Local @Immutable UUID id, Ref<? extends IUser> owner, Ref<@Strong @Mutable Date> date,
                 @Weak @Mutable String text) {
        super(id, owner);
        this.date = date;
        this.text = text;
        this.subscribers = new LinkedList<>();
    }

    public void initSelf(Ref<? extends IEvent> self) {
        this.self = self;
    }

    public void addSubscriber(Ref<? extends @Mutable IUser> user) {
        this.subscribers.add(user);
    }

    @Transactional
    @StrongOp
    public void postUpdate(@Weak @Mutable String text) {
        this.text += "Update (" + new Date() + "): " + text;
        for (Ref<? extends @Mutable IUser> user : subscribers) { // TODO
            user.ref().notifyOfEventUpdate(self);
        }
    }

    @Transactional
    @StrongOp
    public void postUpdate(@Weak @Mutable String text, @Strong @Mutable Date newDate) {
        this.text += "Update (" + new Date() + "): " + text;
        this.date.ref().setTime(newDate.getTime());
        for (Ref<? extends @Mutable IUser> user : subscribers) { // TODO
            user.ref().notifyOfEventUpdate(self);
        }
    }
}
