package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;

public class User implements Serializable {
    private final String id;
    private String name;
    private String email;
    // socials
    // location
    // birthday
    // profile pic
    private String phone;
    private String profileText;
    private final List<Ref<User>> friends;
    private final List<Ref<User>> followers;
    private final List<Ref<User>> following;
    private final List<Ref<User>> receivedFriendRequests;
    private final List<Ref<User>> sentFriendRequests;
    // education history
    // employment history
    private final List<Ref<? extends Activity>> feed;
    private final List<Ref<? extends Activity>> unreadFeed;
    private final List<Ref<Group>> participatingGroups;

    public User(String id, String name) {
        this.id = id;
        this.name = name;
        this.friends = new LinkedList<>();
        this.followers = new LinkedList<>();
        this.following = new LinkedList<>();
        this.receivedFriendRequests = new LinkedList<>();
        this.sentFriendRequests = new LinkedList<>();
        this.feed = new LinkedList<>();
        this.unreadFeed = new LinkedList<>();
        this.participatingGroups = new LinkedList<>();
    }

    public void addActivity(Ref<? extends Activity> status) {
        unreadFeed.add(status);
    }

    @Transactional
    public void notifyOfEventUpdate(Ref<Event> event) {
        feed.removeIf(x -> Util.equalsActivity(x, event));
        unreadFeed.removeIf(x -> Util.equalsActivity(x, event));
        unreadFeed.add(0, event);
    }

    @Transactional
    public void notifyOfGroupMembershipAcceptance(Ref<Group> group) {
        participatingGroups.add(group);
    }

    @Transactional
    public void markActivityAsRead(Ref<? extends Activity> activity) {
        unreadFeed.removeIf(x -> Util.equalsActivity(x, activity));
        feed.add(0, activity);
    }

    public  void addReceivedFriendRequest(Ref<User> sender) {
        receivedFriendRequests.add(sender);
    }

    @Transactional
    public void removeReceivedFriendRequest(Ref<User> sender) {
        receivedFriendRequests.removeIf(x -> Util.equalsUser(x, sender));
    }

    public void addSentFriendRequest(Ref<User> sender) {
        sentFriendRequests.add(sender);
    }

    @Transactional
    public void removeSentFriendRequest(Ref<User> receiver) {
        sentFriendRequests.removeIf(x -> Util.equalsUser(x, receiver));
    }

    public void addFriend(Ref<User> user) {
        friends.add(user);
    }

    @Transactional
    public void removeFriend(Ref<User> user) {
        friends.removeIf(x -> Util.equalsUser(x, user));
    }

    public void addFollower(Ref<User> user) {
        followers.add(user);
    }

    @Transactional
    public void removeFollower(Ref<User> user) {
        followers.removeIf(x -> Util.equalsUser(x, user));
    }

    public void addFollowing(Ref<User> user) {
        following.add(user);
    }

    @Transactional
    public void removeFollowing(Ref<User> user) {
        following.removeIf(x -> Util.equalsUser(x, user));
    }

    public void addParticipatingGroup(Ref<Group> group) {
        participatingGroups.add(group);
    }

    public void changeProfileText(String text) {
        this.profileText = text;
    }

    public void changePhoneNumber(String phone) {
        this.phone = phone;
    }

    public void changeName(String name) {
        this.name = name;
    }

    public void changeEmail(String email) {
        this.email = email;
    }

    public String getId() {
        return id;
    }

    public String getName() {
        return name;
    }

    public String getEmail() {
        return email;
    }

    public String getPhone() {
        return phone;
    }

    public String getProfileText() {
        return profileText;
    }

    public List<Ref<User>> getFriends() {
        return friends;
    }

    public List<Ref<User>> getFollowers() {
        return followers;
    }

    public List<Ref<User>> getFollowing() {
        return following;
    }

    public List<Ref<User>> getReceivedFriendRequests() {
        return receivedFriendRequests;
    }

    public List<Ref<User>> getSentFriendRequests() {
        return sentFriendRequests;
    }

    public List<Ref<? extends Activity>> getFeed() {
        return feed;
    }

    public List<Ref<? extends Activity>> getUnreadFeed() {
        return unreadFeed;
    }

    public List<Ref<Group>> getParticipatingGroups() {
        return participatingGroups;
    }
}
