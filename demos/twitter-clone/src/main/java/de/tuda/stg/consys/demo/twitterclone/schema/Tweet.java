package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;
import java.util.Date;
import java.util.UUID;

public class Tweet implements Serializable {

    private UUID id = UUID.randomUUID();
    private JRef<User> user;
    private String body;
    private Date created = new Date();
    private JRef<@Strong Counter> retweetCount;

    public Tweet(JRef<User>  user, String body, JRef<@Strong Counter> retweetCount) {
        this.user = user;
        this.body = body;
        this.retweetCount = retweetCount;
    }

    public UUID getId() {
        return id;
    }

    public JRef<User> getUser() {
        return user;
    }

    public String getBody() {
        return body;
    }

    public Date getCreated() {
        return created;
    }

    public void retweet() {
        retweetCount.ref().inc();
    }

    @Override
    public String toString() {
        return getUser() + ": " + getBody() + " [" + getCreated() + "]";
    }
}
