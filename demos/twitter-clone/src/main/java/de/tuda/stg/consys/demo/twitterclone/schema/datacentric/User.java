package de.tuda.stg.consys.demo.twitterclone.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.demo.twitterclone.schema.ITweet;
import de.tuda.stg.consys.demo.twitterclone.schema.IUser;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.UUID;

public @Mixed class User implements IUser {
    private final @Immutable UUID id = UUID.randomUUID();
    private final @Immutable String username = id.hashCode() + "";
    private String name;
    private final Date created = new Date();

    private final List<Ref<? extends IUser>> followers = new ArrayList<>();
    private final List<Ref<? extends IUser>> followings = new ArrayList<>();
    private final List<Ref<? extends ITweet>> timeline = new ArrayList<>();
    private final List<Ref<? extends ITweet>> retweets = new ArrayList<>();

    public User(@Mutable @Local String name) {
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

    public List<Ref<? extends IUser>> getFollowers() {
        return followers;
    }

    public List<Ref<? extends IUser>> getFollowings() {
        return followings;
    }

    public List<Ref<? extends ITweet>> getTimeline() { return timeline; }

    public void addFollower(Ref<? extends IUser> follower) {
        followers.add(follower);
    }

    public void addFollowing(Ref<? extends IUser> following) {
        followings.add(following);
    }

    public void removeFollower(Ref<? extends IUser> follower) {
        followers.remove(follower);
    }

    public void removeFollowing(Ref<? extends IUser> following) {
        followings.remove(following);
    }

    @Transactional
    public void addRetweet(Ref<? extends ITweet> tweet) {
        addToTimeline(tweet);
        retweets.add(tweet);
    }

    @Transactional
    public void addToTimeline(Ref<? extends ITweet> tweet) {
        timeline.add(tweet);
        for(Ref<? extends @Mutable IUser> user: followers) {
            user.ref().addToTimeline(tweet);
        }
    }

    @Override
    public String toString() {
        return getId() + " " + getUsername() + " " + getName() + " " + getCreated();
    }
}
