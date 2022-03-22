package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

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
    private final Map<String, Ref<User>> friends;
    private final Map<String, Ref<User>> followers;
    private final Map<String, Ref<User>> following;
    private final Map<String, Ref<User>> receivedFriendRequests;
    private final Map<String, Ref<User>> sentFriendRequests;
    // education history
    // employment history
    private final List<Ref<? extends Post>> feed;
    private final List<Ref<Group>> participatingGroups;

    public User(String id, String name) {
        this.id = id;
        this.name = name;
        this.friends = new HashMap<>();
        this.followers = new HashMap<>();
        this.following = new HashMap<>();
        this.receivedFriendRequests = new HashMap<>();
        this.sentFriendRequests = new HashMap<>();
        this.feed = new LinkedList<>();
        this.participatingGroups = new LinkedList<>();
    }

    public void addPost(Ref<? extends Post> post) {
        feed.add(0, post);
    }

    @Transactional
    @StrongOp
    public void notifyOfEventUpdate(Ref<Event> event) {
        feed.add(0, event); // leads to double entries
    }

    @Transactional
    public void notifyOfGroupMembershipAcceptance(Ref<Group> group) {
        participatingGroups.add(group);
    }

    @Transactional
    public void addReceivedFriendRequest(Ref<User> sender) {
        receivedFriendRequests.put(sender.ref().getId(), sender);
    }

    @Transactional
    public void removeReceivedFriendRequest(Ref<User> sender) {
        receivedFriendRequests.remove(sender.ref().getId());
    }

    @Transactional
    public void addSentFriendRequest(Ref<User> sender) {
        sentFriendRequests.put(sender.ref().getId(), sender);
    }

    @Transactional
    public void removeSentFriendRequest(Ref<User> receiver) {
        sentFriendRequests.remove(receiver.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addFriend(Ref<User> user) {
        friends.put(user.ref().getId(), user);
    }

    @Transactional
    public void removeFriend(Ref<User> user) {
        friends.remove(user.ref().getId());
    }

    @Transactional
    public void addFollower(Ref<User> user) {
        followers.put(user.ref().getId(), user);
    }

    @Transactional
    public void removeFollower(Ref<User> user) {
        followers.remove(user.ref().getId());
    }

    @Transactional
    public void addFollowing(Ref<User> user) {
        following.put(user.ref().getId(), user);
    }

    @Transactional
    public void removeFollowing(Ref<User> user) {
        following.remove(user.ref().getId());
    }

    @StrongOp
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
        return new ArrayList<>(friends.values());
    }

    public List<Ref<User>> getFollowers() {
        return new ArrayList<>(followers.values());
    }

    public List<Ref<User>> getFollowing() {
        return new ArrayList<>(following.values());
    }

    public List<Ref<User>> getReceivedFriendRequests() {
        return new ArrayList<>(receivedFriendRequests.values());
    }

    public List<Ref<User>> getSentFriendRequests() {
        return new ArrayList<>(sentFriendRequests.values());
    }

    public List<Ref<? extends Post>> getNewestPosts(int n) {
        return feed.stream().limit(n).collect(Collectors.toList());
    }

    public List<Ref<Group>> getParticipatingGroups() {
        return participatingGroups;
    }
}
