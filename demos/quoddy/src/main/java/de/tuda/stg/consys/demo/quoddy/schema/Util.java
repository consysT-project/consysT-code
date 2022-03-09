package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;

import java.util.List;

public class Util {
    @Transactional
    public static boolean equalsUser(Ref<User> a, Ref<User> b) {
        return a.ref().getId().equals(b.ref().getId());
    }

    @Transactional
    public static boolean equalsActivity(Ref<? extends Activity> a, Ref<? extends Activity> b) {
        return a.ref().getId().equals(b.ref().getId());
    }

    @Transactional
    public static void acceptFriendRequest(Ref<User> receiver, Ref<User> sender) {
        receiver.ref().removeReceivedFriendRequest(sender);
        sender.ref().removeSentFriendRequest(receiver);
        receiver.ref().addFriend(sender);
        sender.ref().addFriend(receiver);
    }

    @Transactional
    public static void sendFriendRequest(Ref<User> receiver, Ref<User> sender) {
        receiver.ref().addReceivedFriendRequest(sender);
        sender.ref().addSentFriendRequest(receiver);
    }

    @Transactional
    public static void followUser(Ref<User> following, Ref<User> follower) {
        following.ref().addFollower(follower);
        follower.ref().addFollowing(following);
    }

    @Transactional
    public static void stopFollowingUser(Ref<User> following, Ref<User> follower) {
        following.ref().removeFollower(follower);
        follower.ref().removeFollowing(following);
    }

    @Transactional
    public static void postStatusToPersonalProfile(Ref<User> user, Ref<StatusUpdate> status) {
        if (!Util.equalsUser(user, status.ref().getOwner()))
            throw new IllegalArgumentException("can only post own status updates");

        user.ref().addActivity(status);
        for (Ref<User> follower : (List<Ref<User>>)user.ref().getFollowers()) {
            follower.ref().addActivity(status);
        }
        for (Ref<User> friend : (List<Ref<User>>)user.ref().getFriends()) {
            friend.ref().addActivity(status);
        }
    }

    @Transactional
    public static void postStatusToGroup(Ref<Group> group, Ref<StatusUpdate> status) {
        Ref<User> owner = status.ref().getOwner();
        if (!(boolean)group.ref().isUserInGroup(owner))
            throw new IllegalArgumentException("can only post in groups you are a member of");

        group.ref().addActivity(status);
    }

    @Transactional
    public static void shareActivity(Ref<User> receiver, Ref<? extends Activity> activity) {
        receiver.ref().addActivity(activity);
    }

    @Transactional
    public void acceptMembershipRequest(Ref<Group> group, Ref<User> user, Ref<User> sessionUser) {
        group.ref().acceptMembershipRequest(user, sessionUser);
        user.ref().notifyOfGroupMembershipAcceptance(group);
    }


    void mentionUser() {

    }
    void searchUser() {

    }
    void searchGroup() {

    }
}
