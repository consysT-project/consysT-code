package de.tuda.stg.consys.demo.quoddy.schema.opcentric;

import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.quoddy.schema.Comment;
import de.tuda.stg.consys.demo.quoddy.schema.IPost;
import de.tuda.stg.consys.demo.quoddy.schema.IUser;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.UUID;

public @Mixed class Post implements IPost {
    private final @Immutable UUID id;
    private final Ref<? extends IUser> owner;
    private final Date creationTimestamp = new Date();
    private final List<Comment> comments = new LinkedList<>();

    public Post() {
        this.id = null;
        this.owner = null;
    }

    public Post(@Local @Immutable UUID id, Ref<? extends IUser> owner) {
        this.id = id;
        this.owner = owner;
    }

    public void addComment(Comment comment) {
        comments.add(comment);
    }

    @SideEffectFree
    public UUID getId() {
        return id;
    }

    @SideEffectFree
    public Ref<? extends IUser> getOwner() {
        return owner;
    }

    @SideEffectFree
    public Date getCreationTimestamp() {
        return creationTimestamp;
    }

    @SideEffectFree
    public List<Comment> getComments() {
        return comments;
    }
}
