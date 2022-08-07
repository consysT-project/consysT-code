package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

public interface IUser extends Serializable {
    void addPost(Ref<? extends IPost> post);

    @Transactional
    void notifyOfEventUpdate(Ref<? extends IEvent> event);

    @Transactional
    void notifyOfGroupMembershipAcceptance(Ref<? extends IGroup> group);

    @Transactional
    void addReceivedFriendRequest(Ref<? extends IUser> sender);

    @Transactional
    void removeReceivedFriendRequest(Ref<? extends IUser> sender);

    @Transactional
    void addSentFriendRequest(Ref<? extends IUser> sender);

    @Transactional
    void removeSentFriendRequest(Ref<? extends IUser> receiver);

    @StrongOp
    @Transactional
    void addFriend(Ref<? extends IUser> user);

    @StrongOp
    @Transactional
    void removeFriend(Ref<? extends IUser> user);

    @StrongOp
    @Transactional
    void addFollower(Ref<? extends IUser> user);

    @StrongOp
    @Transactional
    void removeFollower(Ref<? extends IUser> user);

    @StrongOp
    @Transactional
    void addFollowing(Ref<? extends IUser> user);

    @StrongOp
    @Transactional
    void removeFollowing(Ref<? extends IUser> user);

    @StrongOp
    void addParticipatingGroup(Ref<? extends IGroup> group);

    void changeProfileText(@Weak @Mutable String text);

    void changePhoneNumber(@Weak @Mutable String phone);

    void changeName(@Weak @Mutable String name);

    void changeEmail(@Weak @Mutable String email);

    @SideEffectFree
    String getId();

    @SideEffectFree
    String getName();

    @SideEffectFree
    String getEmail();

    @SideEffectFree
    String getPhone();

    @SideEffectFree
    String getProfileText();

    @SideEffectFree
    List<Ref<? extends IUser>> getFriends();

    @SideEffectFree
    List<Ref<? extends IUser>> getFollowers();

    @SideEffectFree
    List<Ref<? extends IUser>> getFollowing();

    @SideEffectFree
    List<Ref<? extends IUser>> getReceivedFriendRequests();

    @SideEffectFree
    List<Ref<? extends IUser>> getSentFriendRequests();

    @SideEffectFree
    List<Ref<? extends IPost>> getNewestPosts(int n);

    @SideEffectFree
    List<Ref<? extends IGroup>> getParticipatingGroups();
}
