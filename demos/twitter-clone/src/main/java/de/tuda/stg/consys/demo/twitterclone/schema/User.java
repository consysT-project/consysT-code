package de.tuda.stg.consys.demo.twitterclone.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.UUID;

public class User implements Serializable {

    private UUID id = UUID.randomUUID();
    private String username = id.hashCode() + "";
    private String name;
    private Date created = new Date();

    private List<Ref<User>> followers = new ArrayList<>();
    private List<Ref<User>> followings = new ArrayList<>();
    private List<Ref<Tweet>> timeline = new ArrayList<>();
    private List<Ref<Tweet>> retweets = new ArrayList<>();

    public User(String name) {
        this.name = name;
    }

    public UUID getId() {
        return id;
    }

    public String getUsername() {
        return username;
    }

    public String getName() {
        return name;
    }

    public Date getCreated() {
        return created;
    }

    public List<Ref<User>> getFollowers() {
        return followers;
    }

    public List<Ref<User>> getFollowings() {
        return followings;
    }

    public List<Ref<Tweet>> getTimeline() { return timeline; }

    public void addFollower(Ref<User> follower) {
        followers.add(follower);
    }

    public void addFollowing(Ref<User> following) {
        followings.add(following);
    }

    public void removeFollower(Ref<User> follower) {
        followers.remove(follower);
    }

    public void removeFollowing(Ref<User> following) {
        followings.remove(following);
    }

    public void addRetweet(Ref<Tweet> tweet) {
        addToTimeline(tweet);
        retweets.add(tweet);
    }

    @Transactional
    public void addToTimeline(Ref<Tweet> tweet) {
        timeline.add(tweet);
        for(Ref<User> user: followers) {
            user.ref().addToTimeline(tweet);
        }
    }

    @Override
    public java.lang.String toString() {
        return getId() + " " + getUsername() + " " + getName() + " " + getCreated();
    }
}
