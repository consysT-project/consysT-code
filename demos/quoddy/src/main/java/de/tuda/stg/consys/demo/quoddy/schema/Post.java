package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.UUID;

public class Post implements Serializable {
    private final UUID id;
    private final Ref<User> owner;
    private final Date creationTimestamp;
    private final List<Comment> comments;

    public Post(UUID id, Ref<User> owner) {
        this.id = id;
        this.owner = owner;
        this.comments = new LinkedList<>();
        this.creationTimestamp = new Date();
    }

    public void addComment(Comment comment) {
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

    public List<Comment> getComments() {
        return comments;
    }
}
