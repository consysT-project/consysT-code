package demos.twitter.consystop;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import java.io.Serializable;
import java.util.*;

public @Weak class User implements Serializable {

    private @Immutable UUID id = UUID.randomUUID();
    private @Immutable String username = (((@Mutable UUID) id).hashCode()) + "";
    private String name;
    private Date created = new Date();

    private List<Ref<@Mutable User>> followers = new ArrayList<>();
    private List<Ref<User>> followings = new ArrayList<>();
    private List<Ref<Tweet>> timeline = new ArrayList<>();
    private List<Ref<Tweet>> retweets = new ArrayList<>();

    public User(@Mutable @Weak String name) {
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

    public List<Ref<@Mutable User>> getFollowers() {
        return followers;
    }

    public List<Ref<User>> getFollowings() {
        return followings;
    }

    public List<Ref<Tweet>> getTimeline() {
        return timeline;
    }

    public void addFollower(Ref<@Mutable User> follower) {
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

    @Transactional
    public void addRetweet(Ref<@Mutable Tweet> tweet) {
        addToTimeline(tweet);
        retweets.add(tweet);
        tweet.ref().retweet();
    }

    @Transactional
    public void addToTimeline(Ref<Tweet> tweet) {
        timeline.add(tweet);
        for(Ref<@Mutable User> user: followers) {
            user.ref().addToTimeline(tweet);
        }
    }

    @Override
    public java.lang.String toString() {
        return getId() + " " + getUsername() + " " + getName() + " " + getCreated();
    }
}
