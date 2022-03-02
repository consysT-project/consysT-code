package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.UUID;

public class Activity implements Serializable {
    private final UUID id;
    private final Ref<User> owner;
    private final Date creationTimestamp;
    private final List<Ref<Comment>> comments;

    public Activity(UUID id, Ref<User> owner) {
        this.id = id;
        this.owner = owner;
        this.comments = new LinkedList<>();
        this.creationTimestamp = new Date();
    }

    void addComment(Ref<Comment> comment) {
        comments.add(comment);
    }

    public UUID getId() {
        return id;
    }

    public Ref<User> getOwner() {
        return owner;
    }

    public Date getCreationTimestamp() {
        return creationTimestamp;
    }

    public List<Ref<Comment>> getComments() {
        return comments;
    }
}
