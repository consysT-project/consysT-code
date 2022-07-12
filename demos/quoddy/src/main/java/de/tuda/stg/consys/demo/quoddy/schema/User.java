package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;
import java.util.stream.Collectors;

public @Mixed class User implements Serializable {
    private final @Immutable String id;
    private String name = "";
    private String email = "";
    // socials
    // location
    // birthday
    // profile pic
    private String phone = "";
    private String profileText = "";
    private final Map<String, Ref<User>> friends = new HashMap<>();
    private final Map<String, Ref<User>> followers = new HashMap<>();
    private final Map<String, Ref<User>> following = new HashMap<>();
    private final Map<String, Ref<User>> receivedFriendRequests = new HashMap<>();
    private final Map<String, Ref<User>> sentFriendRequests = new HashMap<>();
    // education history
    // employment history
    private final List<Ref<? extends Post>> feed = new LinkedList<>();
    private final List<Ref<Group>> participatingGroups = new LinkedList<>();

    public User() {
        id = null;
    }

    public User(@Local @Immutable String id, @Mutable @Weak String name) {
        this.id = id;
        this.name = name;
    }

    public void addPost(Ref<? extends Post> post) {
        feed.add(0, post);
    }

    @Transactional
    public void notifyOfEventUpdate(Ref<Event> event) {
        feed.add(0, event);
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

    @StrongOp
    @Transactional
    public void removeFriend(Ref<User> user) {
        friends.remove(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addFollower(Ref<User> user) {
        followers.put(user.ref().getId(), user);
    }

    @StrongOp
    @Transactional
    public void removeFollower(Ref<User> user) {
        followers.remove(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addFollowing(Ref<User> user) {
        following.put(user.ref().getId(), user);
    }

    @StrongOp
    @Transactional
    public void removeFollowing(Ref<User> user) {
        following.remove(user.ref().getId());
    }

    @StrongOp
    public void addParticipatingGroup(Ref<Group> group) {
        participatingGroups.add(group);
    }

    public void changeProfileText(@Weak @Mutable String text) {
        this.profileText = text;
    }

    public void changePhoneNumber(@Weak @Mutable String phone) {
        this.phone = phone;
    }

    public void changeName(@Weak @Mutable String name) {
        this.name = name;
    }

    public void changeEmail(@Weak @Mutable String email) {
        this.email = email;
    }

    @SideEffectFree
    public String getId() {
        return id;
    }

    @SideEffectFree
    public String getName() {
        return name;
    }

    @SideEffectFree
    public String getEmail() {
        return email;
    }

    @SideEffectFree
    public String getPhone() {
        return phone;
    }

    @SideEffectFree
    public String getProfileText() {
        return profileText;
    }

    @SideEffectFree
    public List<Ref<User>> getFriends() {
        return new ArrayList<>(friends.values());
    }

    @SideEffectFree
    public List<Ref<User>> getFollowers() {
        return new ArrayList<>(followers.values());
    }

    @SideEffectFree
    public List<Ref<User>> getFollowing() {
        return new ArrayList<>(following.values());
    }

    @SideEffectFree
    public List<Ref<User>> getReceivedFriendRequests() {
        return new ArrayList<>(receivedFriendRequests.values());
    }

    @SideEffectFree
    public List<Ref<User>> getSentFriendRequests() {
        return new ArrayList<>(sentFriendRequests.values());
    }

    @SideEffectFree
    public List<Ref<? extends Post>> getNewestPosts(int n) {
        return (@Weak @Immutable List<Ref<? extends Post>>) feed.subList(0, Math.min(n, feed.size()));
    }

    @SideEffectFree
    public List<Ref<Group>> getParticipatingGroups() {
        return participatingGroups;
    }
}
