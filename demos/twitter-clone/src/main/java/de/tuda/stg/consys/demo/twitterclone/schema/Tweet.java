package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public class Tweet implements Serializable {

    private UUID id = UUID.randomUUID();
    private Ref<User> user;
    private String body;
    private Date created = new Date();
    private Ref<@Strong Counter> retweetCount;

    public Tweet() {}

    public Tweet(Ref<User>  user, String body, Ref<@Strong Counter> retweetCount) {
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
