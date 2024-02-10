package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.japi.Ref;

public class Util {
    @Transactional
    public static boolean equalsUser(Ref<? extends IUser> a, Ref<? extends IUser> b) {
        return a.ref().getId().equals(b.ref().getId());
    }

    @Transactional
    public static boolean equalsActivity(Ref<? extends IPost> a, Ref<? extends IPost> b) {
        return a.ref().getId().equals(b.ref().getId());
    }

    @Transactional
    public static void acceptFriendRequest(Ref<? extends @Mutable IUser> receiver, Ref<? extends @Mutable IUser> sender) {
        receiver.ref().removeReceivedFriendRequest(sender);
        sender.ref().removeSentFriendRequest(receiver);
        receiver.ref().addFriend(sender);
        sender.ref().addFriend(receiver);
    }

    @Transactional
    public static void stopFollowingUser(Ref<? extends @Mutable IUser> following, Ref<? extends @Mutable IUser> follower) {
        following.ref().removeFollower(follower);
        follower.ref().removeFollowing(following);
    }

    @Transactional
    public void acceptMembershipRequest(Ref<? extends @Mutable IGroup> group, Ref<? extends @Mutable IUser> user, Ref<? extends IUser> sessionUser) {
        group.ref().acceptMembershipRequest(user, sessionUser);
        user.ref().notifyOfGroupMembershipAcceptance(group);
    }
}
