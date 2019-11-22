package de.tuda.stg.consys.twitterclone.schema;

import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicated;

import java.io.Serializable;
import java.util.*;

public class User implements JReplicated {

    /* Needed for JReplicated */
    public transient AkkaReplicaSystem<String> replicaSystem = null;


    private UUID id = UUID.randomUUID();
    private String username = id.hashCode() + "";
    private String name;
    private Date created = new Date();

    private List<JRef<User>> followers = new ArrayList<>();
    private List<JRef<User>> followings = new ArrayList<>();
    private List<JRef<Tweet>> timeline = new ArrayList<>();
    private List<JRef<Tweet>> retweets = new ArrayList<>();

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

    public List<JRef<User>> getFollowers() {
        return followers;
    }

    public List<JRef<User>> getFollowings() {
        return followings;
    }

    public void addFollower(JRef<User> follower) {
        followers.add(follower);
    }

    public void addFollowing(JRef<User> following) {
        followings.add(following);
    }

    public void removeFollower(JRef<User> follower) {
        followers.remove(follower);
    }

    public void removeFollowing(JRef<User> following) {
        followings.remove(following);
    }

    public void addRetweet(JRef<Tweet> tweet) {
        addToTimeline(tweet);
        retweets.add(tweet);
    }

    public void addToTimeline(JRef<Tweet> tweet) {
        timeline.add(tweet);
        for(JRef<User> user: followers) {
            getSystem().ifPresent(system -> {
                user.setReplicaSystem(replicaSystem);
                user.ref().addToTimeline(tweet);
            });
        }
    }

    @Override
    public java.lang.String toString() {
        return getId() + " " + getUsername() + " " + getName() + " " + getCreated();
    }
}
