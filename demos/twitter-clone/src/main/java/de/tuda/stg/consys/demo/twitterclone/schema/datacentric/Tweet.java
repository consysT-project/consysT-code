package de.tuda.stg.consys.demo.twitterclone.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.twitterclone.schema.ITweet;
import de.tuda.stg.consys.japi.Ref;

import java.util.Date;
import java.util.UUID;

public @Mixed class Tweet implements ITweet {

    private final @Immutable UUID id = UUID.randomUUID();
    private final Ref<User> user;
    private final @Weak String body;
    private final Date created = new Date();
    private final Ref<@Mutable @Strong Counter> retweetCount;

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
    public int getRetweets() {
        return retweetCount.ref().get();
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
