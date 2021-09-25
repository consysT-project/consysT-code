package demos.twitter.java;

import java.util.*;

public class User {

    private UUID id = UUID.randomUUID();
    private String username = id.hashCode() + "";
    private String name;
    private Date created = new Date();

    private List<User> followers = new ArrayList<>();
    private List<User> followings = new ArrayList<>();
    private List<Tweet> timeline = new ArrayList<>();
    private List<Tweet> retweets = new ArrayList<>();

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

    public List<User> getFollowers() {
        return followers;
    }

    public List<User> getFollowings() {
        return followings;
    }

    public List<Tweet> getTimeline() {
        return timeline;
    }

    public void addFollower(User follower) {
        followers.add(follower);
    }

    public void addFollowing(User following) {
        followings.add(following);
    }

    public void removeFollower(User follower) {
        followers.remove(follower);
    }

    public void removeFollowing(User following) {
        followings.remove(following);
    }

    public void addRetweet(Tweet tweet) {
        addToTimeline(tweet);
        retweets.add(tweet);
        tweet.retweet();
    }

    public void addToTimeline(Tweet tweet) {
        timeline.add(tweet);
        for(User user: followers) {
            user.addToTimeline(tweet);
        }
    }

    @Override
    public java.lang.String toString() {
        return getId() + " " + getUsername() + " " + getName() + " " + getCreated();
    }
}
