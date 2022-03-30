package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.japi.Ref;

public class Util {
    @Transactional
    public static boolean equalsUser(Ref<User> a, Ref<User> b) {
        return a.ref().getId().equals(b.ref().getId());
    }

    @Transactional
    public static boolean equalsActivity(Ref<? extends Post> a, Ref<? extends Post> b) {
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
    public static void stopFollowingUser(Ref<User> following, Ref<User> follower) {
        following.ref().removeFollower(follower);
        follower.ref().removeFollowing(following);
    }

    @Transactional
    public void acceptMembershipRequest(Ref<Group> group, Ref<User> user, Ref<User> sessionUser) {
        group.ref().acceptMembershipRequest(user, sessionUser);
        user.ref().notifyOfGroupMembershipAcceptance(group);
    }
}
