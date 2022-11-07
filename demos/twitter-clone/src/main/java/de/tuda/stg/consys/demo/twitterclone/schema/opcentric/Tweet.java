package de.tuda.stg.consys.demo.twitterclone.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.twitterclone.schema.ITweet;
import de.tuda.stg.consys.japi.Ref;

import java.util.Date;
import java.util.UUID;

public @Mixed class Tweet implements ITweet {
    private final @Immutable UUID id = UUID.randomUUID();
    private Ref<User> user;
    private @Weak String body;
    private final Date created = new Date();
    private int retweetCount;

    public Tweet() {}

    public Tweet(Ref<User> user, @Mutable @Weak String body) {
        this.user = user;
        this.body = body;
    }

    public UUID getId() {
        return id;
    }

    public Ref<User> getUser() {
        return user;
    }

    public String getBody() {
        return body;
    }

    public Date getCreated() {
        return created;
    }

    public int getRetweets() {
        return retweetCount;
    }

    @Transactional
    @StrongOp
    public void retweet() {
        retweetCount++;
    }

    @Override
    public String toString() {
        return getUser() + ": " + getBody() + " [" + getCreated() + "]" + "(" + retweetCount + " retweets)";
    }
}
