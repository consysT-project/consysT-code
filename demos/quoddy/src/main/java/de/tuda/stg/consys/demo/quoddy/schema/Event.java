package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.japi.Ref;

import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.UUID;

public class Event extends Post {
    private Date date;
    private final List<Ref<User>> subscribers;

    public Event(UUID id, Ref<User> owner, Date date) {
        super(id, owner);
        this.date = date;
        this.subscribers = new LinkedList<>();
    }

    public void addSubscriber(Ref<User> user) {
        this.subscribers.add(user);
    }

    public void notifySubscribers() {
        // TODO
    }
}
