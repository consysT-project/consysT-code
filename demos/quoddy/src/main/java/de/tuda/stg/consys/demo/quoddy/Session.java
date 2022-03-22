package de.tuda.stg.consys.demo.quoddy;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.quoddy.schema.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Function1;
import scala.Option;

import java.util.Date;
import java.util.List;
import java.util.UUID;


public class Session {
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel;
    public static ConsistencyLevel<CassandraStore> groupConsistencyLevel;
    public static ConsistencyLevel<CassandraStore> activityConsistencyLevel;
    private CassandraStoreBinding store;
    private Ref<User> user;

    public Session(CassandraStoreBinding store) {
        this.store = store;
    }

    public void switchStore(CassandraStoreBinding store) {
        this.store = store;
    }

    private <U> Option<U> doTransaction(CassandraTransactionContextBinding transaction,
                                  Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
    }

    public Ref<User> getUser() {
        return user;
    }

    public Ref<User> registerUser(CassandraTransactionContextBinding tr,
                                  String id, String name) {
        this.user = doTransaction(tr,
                ctx -> Option.apply(ctx.replicate(id, userConsistencyLevel, User.class, id, name))).get();
        return this.user;
    }

    public Option<Ref<User>> lookupUser(CassandraTransactionContextBinding tr,
                                String id) {
        return doTransaction(tr, ctx -> Option.apply(ctx.lookup(id, userConsistencyLevel, User.class)));
    }

    public Ref<Group> createGroup(CassandraTransactionContextBinding tr,
                                  String id, String name, String description, boolean requiresJoinConfirmation) {
        checkLogin();
        return doTransaction(tr, ctx -> {
            Ref<Group> group = ctx.replicate(id, groupConsistencyLevel, Group.class, id, name, description,
                    requiresJoinConfirmation, this.user);
            user.ref().addParticipatingGroup(group);
            return Option.apply(group);
        }).get();
    }

    public Option<Ref<Group>> lookupGroup(CassandraTransactionContextBinding tr,
                                        String id) {
        return doTransaction(tr, ctx -> Option.apply(ctx.lookup(id, groupConsistencyLevel, Group.class)));
    }

    public void joinGroup(CassandraTransactionContextBinding tr,
                          Ref<Group> group) {
        checkLogin();
        doTransaction(tr, ctx -> {
            group.ref().join(user);
            user.ref().addParticipatingGroup(group);
            return Option.empty();
        });
    }

    public void postStatusToProfile(CassandraTransactionContextBinding tr,
                                    String text) {
        checkLogin();
        var id = UUID.randomUUID();

        doTransaction(tr, ctx -> {
            Ref<StatusUpdate> status =
                    ctx.replicate(id.toString(), activityConsistencyLevel, StatusUpdate.class, id, this.user, text);

            this.user.ref().addPost(status);
            for (Ref<User> follower : (List<Ref<User>>)user.ref().getFollowers()) {
                follower.ref().addPost(status); // TODO: could lead to batch too large
            }
            for (Ref<User> friend : (List<Ref<User>>)user.ref().getFriends()) {
                friend.ref().addPost(status); // TODO: could lead to batch too large
            }

            return Option.empty();
        });
    }

    public void postStatusToGroup(CassandraTransactionContextBinding tr,
                                  String text, Ref<Group> group) {
        checkLogin();
        var id = UUID.randomUUID();

        doTransaction(tr, ctx -> {
            Ref<StatusUpdate> status =
                    ctx.replicate(id.toString(), activityConsistencyLevel, StatusUpdate.class, id, this.user, text);

            if (!(boolean)group.ref().isUserInGroup(this.user))
                throw new IllegalArgumentException("can only post in groups you are a member of");

            group.ref().addPost(status);

            return Option.empty();
        });
    }

    public Ref<Event> postEventToGroup(CassandraTransactionContextBinding tr,
                                 String text, Date date, Ref<Group> group) {
        checkLogin();
        var id = UUID.randomUUID();

        return doTransaction(tr, ctx -> {
            Ref<Event> event =
                    ctx.replicate(id.toString(), activityConsistencyLevel, Event.class, id, this.user, date, text);
            event.ref().initSelf(event);

            if (!(boolean)group.ref().isUserInGroup(this.user))
                throw new IllegalArgumentException("can only post in groups you are a member of");

            group.ref().addPost(event);

            return Option.apply(event);
        }).get();
    }

    public void sharePostWithFriend(CassandraTransactionContextBinding tr,
                                    Ref<User> friend, Ref<? extends Post> post) {
        checkLogin();
        doTransaction(tr, ctx -> {
            if (((List<Ref<User>>)this.user.ref().getFriends()).stream().noneMatch(x -> Util.equalsUser(x, friend)))
                throw new IllegalArgumentException("target is not friend of user");
            friend.ref().addPost(post);
            return Option.empty();
        });
    }

    public void sendFriendRequest(CassandraTransactionContextBinding tr,
                                  Ref<User> receiver) {
        checkLogin();
        doTransaction(tr, ctx -> {
            receiver.ref().addReceivedFriendRequest(this.user);
            this.user.ref().addSentFriendRequest(receiver);
            return Option.empty();
        });
    }

    public boolean acceptFriendRequest(CassandraTransactionContextBinding tr, int requestIndex) {
        checkLogin();
        return doTransaction(tr, ctx -> {
            List<Ref<User>> requests = this.user.ref().getReceivedFriendRequests();
            if (requestIndex >= requests.size()) {
                return Option.apply(false);
            }

            Ref<User> sender = requests.get(requestIndex);
            Util.acceptFriendRequest(this.user, sender);

            return Option.apply(true);
        }).get();
    }

    public void follow(CassandraTransactionContextBinding tr, Ref<User> target) {
        checkLogin();
        doTransaction(tr, ctx -> {
            target.ref().addFollower(this.user);
            this.user.ref().addFollowing(target);
            return Option.empty();
        });
    }

    private void checkLogin() {
        if (this.user == null) {
            throw new IllegalStateException("no user is logged in for this session");
        }
    }
}
