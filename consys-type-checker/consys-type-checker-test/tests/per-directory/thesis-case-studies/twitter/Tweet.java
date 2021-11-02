package demos.twitter.consystop;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import java.io.Serializable;
import java.util.*;

public @Mixed class Tweet implements Serializable {

    private @Immutable UUID id = UUID.randomUUID();
    private Ref<User> user;
    private String body;
    private Date created = new Date();
    private int retweetCount;

    public Tweet(Ref<User> user, @Mutable @Local String body) {
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

    @StrongOp
    public void retweet() {
        retweetCount++;
    }

    public int getRetweets() {
        return retweetCount;
    }

    @Override
    public String toString() {
        return getUser() + ": " + getBody() + " [" + getCreated() + "]";
    }
}
