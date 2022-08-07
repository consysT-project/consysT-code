package de.tuda.stg.consys.demo.quoddy.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.quoddy.schema.IEvent;
import de.tuda.stg.consys.demo.quoddy.schema.IGroup;
import de.tuda.stg.consys.demo.quoddy.schema.IPost;
import de.tuda.stg.consys.demo.quoddy.schema.IUser;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.*;

public @Mixed class User implements IUser {
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
    private final List<Ref<? extends IPost>> feed = new LinkedList<>();
    private final List<Ref<? extends IGroup>> participatingGroups = new LinkedList<>();

    public User() {
        id = null;
    }

    public User(@Local @Immutable String id, @Mutable @Weak String name) {
        this.id = id;
        this.name = name;
    }

    public void addPost(Ref<? extends IPost> post) {
        feed.add(0, post);
    }

    @Transactional
    public void notifyOfEventUpdate(Ref<? extends IEvent> event) {
        feed.add(0, event);
    }

    @Transactional
    public void notifyOfGroupMembershipAcceptance(Ref<? extends IGroup> group) {
        participatingGroups.add(group);
    }

    @Transactional
    public void addReceivedFriendRequest(Ref<? extends IUser> sender) {
        receivedFriendRequests.put(sender.ref().getId(), toUserImpl(sender));
    }

    @Transactional
    public void removeReceivedFriendRequest(Ref<? extends IUser> sender) {
        receivedFriendRequests.remove(sender.ref().getId());
    }

    @Transactional
    public void addSentFriendRequest(Ref<? extends IUser> sender) {
        sentFriendRequests.put(sender.ref().getId(), toUserImpl(sender));
    }

    @Transactional
    public void removeSentFriendRequest(Ref<? extends IUser> receiver) {
        sentFriendRequests.remove(receiver.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addFriend(Ref<? extends IUser> user) {
        friends.put(user.ref().getId(), toUserImpl(user));
    }

    @StrongOp
    @Transactional
    public void removeFriend(Ref<? extends IUser> user) {
        friends.remove(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addFollower(Ref<? extends IUser> user) {
        followers.put(user.ref().getId(), toUserImpl(user));
    }

    @StrongOp
    @Transactional
    public void removeFollower(Ref<? extends IUser> user) {
        followers.remove(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addFollowing(Ref<? extends IUser> user) {
        following.put(user.ref().getId(), toUserImpl(user));
    }

    @StrongOp
    @Transactional
    public void removeFollowing(Ref<? extends IUser> user) {
        following.remove(user.ref().getId());
    }

    @StrongOp
    public void addParticipatingGroup(Ref<? extends IGroup> group) {
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
    public List<Ref<? extends IUser>> getFriends() {
        return new ArrayList<>(friends.values());
    }

    @SideEffectFree
    public List<Ref<? extends IUser>> getFollowers() {
        return new ArrayList<>(followers.values());
    }

    @SideEffectFree
    public List<Ref<? extends IUser>> getFollowing() {
        return new ArrayList<>(following.values());
    }

    @SideEffectFree
    public List<Ref<? extends IUser>> getReceivedFriendRequests() {
        return new ArrayList<>(receivedFriendRequests.values());
    }

    @SideEffectFree
    public List<Ref<? extends IUser>> getSentFriendRequests() {
        return new ArrayList<>(sentFriendRequests.values());
    }

    @SideEffectFree
    public List<Ref<? extends IPost>> getNewestPosts(int n) {
        return (@Weak @Immutable List<Ref<? extends IPost>>) feed.subList(0, Math.min(n, feed.size()));
    }

    @SideEffectFree
    public List<Ref<? extends IGroup>> getParticipatingGroups() {
        return (List<Ref<? extends IGroup>>) participatingGroups;
    }

    private Ref<User> toUserImpl(Ref<? extends IUser> user) {
        return (Ref<User>) user;
    }
}
