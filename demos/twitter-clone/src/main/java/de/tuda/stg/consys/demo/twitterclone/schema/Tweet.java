package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public @Mixed class Tweet implements Serializable {

    private @Immutable UUID id = UUID.randomUUID();
    private Ref<User> user;
    private @Weak String body;
    private Date created = new Date();
    private Ref<@Mutable @Strong Counter> retweetCount;

    public Tweet() {}

    public Tweet(Ref<User> user, @Mutable @Weak String body, Ref<@Mutable @Strong Counter> retweetCount) {
        this.user = user;
        this.body = body;
        this.retweetCount = retweetCount;
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

    @Transactional
    public void retweet() {
        retweetCount.ref().inc();
    }

    @Override
    public String toString() {
        return getUser() + ": " + getBody() + " [" + getCreated() + "]";
    }
}
