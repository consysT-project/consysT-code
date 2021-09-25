package demos.twitter.java;

import java.util.*;

public class Tweet {

    private UUID id = UUID.randomUUID();
    private User user;
    private String body;
    private Date created = new Date();
    private int retweetCount;

    public Tweet(User user, String body) {
        this.user = user;
        this.body = body;
        this.retweetCount = 0;
    }

    public UUID getId() {
        return id;
    }

    public User getUser() {
        return user;
    }

    public String getBody() {
        return body;
    }

    public Date getCreated() {
        return created;
    }

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
