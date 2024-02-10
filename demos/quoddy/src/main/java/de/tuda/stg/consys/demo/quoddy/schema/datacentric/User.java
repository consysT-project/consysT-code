package de.tuda.stg.consys.demo.quoddy.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.quoddy.schema.IEvent;
import de.tuda.stg.consys.demo.quoddy.schema.IGroup;
import de.tuda.stg.consys.demo.quoddy.schema.IPost;
import de.tuda.stg.consys.demo.quoddy.schema.IUser;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.util.*;

public @Weak class User implements IUser {
    private final @Immutable String id;
    private String name = "";
    private String email = "";
    // socials
    // location
    // birthday
    // profile pic
    private String phone = "";
    private String profileText = "";
    private final Ref<@Mutable RefMap<String, Ref<User>>> friends;
    private final Ref<@Mutable RefMap<String, Ref<User>>> followers;
    private final Ref<@Mutable RefMap<String, Ref<User>>> following;
    private final Map<String, Ref<User>> receivedFriendRequests = new HashMap<>();
    private final Map<String, Ref<User>> sentFriendRequests = new HashMap<>();
    // education history
    // employment history
    private final List<Ref<? extends IPost>> feed = new LinkedList<>();
    private final Ref<@Mutable RefList<Ref<? extends IGroup>>> participatingGroups;

    public User(@Local @Immutable String id, @Mutable @Weak String name,
                Ref<@Mutable RefMap<String, Ref<User>>> friends,
                Ref<@Mutable RefMap<String, Ref<User>>> followers,
                Ref<@Mutable RefMap<String, Ref<User>>> following,
                Ref<@Mutable RefList<Ref<? extends IGroup>>> participatingGroups) {
        this.id = id;
        this.name = name;
        this.friends = friends;
        this.followers = following;
        this.following = followers;
        this.participatingGroups = participatingGroups;
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
        participatingGroups.ref().add(group);
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
        friends.ref().put(user.ref().getId(), toUserImpl(user));
    }

    @StrongOp
    @Transactional
    public void removeFriend(Ref<? extends IUser> user) {
        friends.ref().remove(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addFollower(Ref<? extends IUser> user) {
        followers.ref().put(user.ref().getId(), toUserImpl(user));
    }

    @StrongOp
    @Transactional
    public void removeFollower(Ref<? extends IUser> user) {
        followers.ref().remove(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addFollowing(Ref<? extends IUser> user) {
        following.ref().put(user.ref().getId(), toUserImpl(user));
    }

    @StrongOp
    @Transactional
    public void removeFollowing(Ref<? extends IUser> user) {
        following.ref().remove(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void addParticipatingGroup(Ref<? extends IGroup> group) {
        participatingGroups.ref().add(group);
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

    @SideEffectFree @Transactional
    public List<Ref<? extends IUser>> getFriends() {
        return new ArrayList<>(friends.ref().values());
    }

    @SideEffectFree @Transactional
    public List<Ref<? extends IUser>> getFollowers() {
        return new ArrayList<>(followers.ref().values());
    }

    @SideEffectFree @Transactional
    public List<Ref<? extends IUser>> getFollowing() {
        return new ArrayList<>(following.ref().values());
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

    @SideEffectFree @Transactional
    public List<Ref<? extends IGroup>> getParticipatingGroups() {
        return new ArrayList<>(participatingGroups.ref().get());
    }

    @SuppressWarnings("unchecked")
    private Ref<User> toUserImpl(Ref<? extends IUser> user) {
        return (Ref<User>) user;
    }
}
