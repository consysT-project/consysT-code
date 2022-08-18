package de.tuda.stg.consys.demo.quoddy;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.quoddy.schema.*;
import de.tuda.stg.consys.demo.quoddy.schema.datacentric.BoolBox;
import de.tuda.stg.consys.demo.quoddy.schema.datacentric.RefList;
import de.tuda.stg.consys.demo.quoddy.schema.datacentric.RefMap;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Function1;
import scala.Option;

import java.util.Date;
import java.util.List;
import java.util.UUID;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.STRONG;

@SuppressWarnings({"consistency"})
public class Session {
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel;
    public static ConsistencyLevel<CassandraStore> groupConsistencyLevel;
    public static ConsistencyLevel<CassandraStore> activityConsistencyLevel;

    public static Class<? extends IGroup> groupImpl;
    public static Class<? extends IUser> userImpl;
    public static Class<? extends IStatusUpdate> statusUpdateImpl;
    public static Class<? extends IEvent> eventImpl;

    public static boolean dataCentric;

    private CassandraStoreBinding store;
    private Ref<? extends IUser> user;

    public Session(CassandraStoreBinding store) {
        this.store = store;
    }

    public void setStore(CassandraStoreBinding store) {
        this.store = store;
    }

    private <U> Option<U> doTransaction(CassandraTransactionContextBinding transaction,
                                  Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
    }

    public Ref<? extends IUser> getUser() {
        return user;
    }

    public Ref<? extends IUser> registerUser(CassandraTransactionContextBinding tr,
                                  String id, String name) {
        if (dataCentric) {
            this.user = doTransaction(tr, ctx -> {
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> friends =
                        ctx.replicate(id + ":friends", STRONG, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> followers =
                        ctx.replicate(id + ":followers", STRONG, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> following =
                        ctx.replicate(id + ":following", STRONG, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefList<Ref<? extends IGroup>>> groups =
                        ctx.replicate(id + ":groups", STRONG, (Class<RefList<Ref<? extends IGroup>>>)(Class)RefList.class);
                return Option.apply(ctx.replicate(id, userConsistencyLevel, userImpl, id, name, friends, followers, following, groups));
            }).get();
        } else {
            this.user = doTransaction(tr,
                    ctx -> Option.apply(ctx.replicate(id, userConsistencyLevel, userImpl, id, name))).get();
        }
        return this.user;
    }

    public Option<Ref<? extends IUser>> lookupUser(CassandraTransactionContextBinding tr,
                                String id) {
        return doTransaction(tr, ctx -> Option.apply(ctx.lookup(id, userConsistencyLevel, userImpl)));
    }

    public Ref<? extends IGroup> createGroup(CassandraTransactionContextBinding tr,
                                  String id, String name, String description, boolean requiresJoinConfirmation) {
        checkLogin();
        return doTransaction(tr, ctx -> {
            Ref<? extends IGroup> group;
            if (dataCentric) {
                Ref<@Strong @Mutable BoolBox> requires =
                        ctx.replicate(id + ":requires", STRONG, BoolBox.class, requiresJoinConfirmation);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> owners =
                        ctx.replicate(id + ":owners", STRONG, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> members =
                        ctx.replicate(id + ":members", STRONG, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> pending =
                        ctx.replicate(id + ":pending", STRONG, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                group = ctx.replicate(id, groupConsistencyLevel, groupImpl, id, name, description,
                        requires, this.user, owners, members, pending);
            } else {
                group = ctx.replicate(id, groupConsistencyLevel, groupImpl, id, name, description,
                        requiresJoinConfirmation, this.user);
            }
            user.ref().addParticipatingGroup(group);
            return Option.apply(group);
        }).get();
    }

    public Option<Ref<? extends IGroup>> lookupGroup(CassandraTransactionContextBinding tr,
                                        String id) {
        return doTransaction(tr, ctx -> Option.apply(ctx.lookup(id, groupConsistencyLevel, groupImpl)));
    }

    public void joinGroup(CassandraTransactionContextBinding tr,
                          Ref<? extends IGroup> group) {
        checkLogin();
        doTransaction(tr, ctx -> {
            group.ref().join(user);
            user.ref().addParticipatingGroup(group);
            return Option.apply(0);
        });
    }

    public void postStatusToProfile(CassandraTransactionContextBinding tr,
                                    String text) {
        checkLogin();
        var id = UUID.randomUUID();

        doTransaction(tr, ctx -> {
            Ref<? extends IStatusUpdate> status =
                    ctx.replicate(id.toString(), activityConsistencyLevel, statusUpdateImpl, id, this.user, text);

            this.user.ref().addPost(status);
            for (Ref<? extends IUser> follower : user.ref().getFollowers()) {
                follower.ref().addPost(status); // TODO: could lead to batch too large
            }
            // cyclic dependency for all-strong case: if two friends post simultaneously, they end up waiting for each
            // other's locks here
            // TODO: for some reason also happens for data-centric mixed case?
            for (Ref<? extends IUser> friend : user.ref().getFriends()) {
                friend.ref().addPost(status); // TODO: could lead to batch too large
            }

            return Option.apply(0);
        });
    }

    public void postStatusToGroup(CassandraTransactionContextBinding tr,
                                  String text, Ref<? extends IGroup> group) {
        checkLogin();
        var id = UUID.randomUUID();

        doTransaction(tr, ctx -> {
            Ref<? extends IStatusUpdate> status =
                    ctx.replicate(id.toString(), activityConsistencyLevel, statusUpdateImpl, id, this.user, text);

            if (!(boolean)group.ref().isUserInGroup(this.user))
                throw new IllegalArgumentException("can only post in groups you are a member of");

            group.ref().addPost(status);

            return Option.apply(0);
        });
    }

    public Ref<? extends IEvent> postEventToGroup(CassandraTransactionContextBinding tr,
                                       String text, Date date, Ref<? extends IGroup> group) {
        checkLogin();
        var id = UUID.randomUUID();

        return doTransaction(tr, ctx -> {
            Ref<? extends IEvent> event;
            if (dataCentric) {
                Ref<@Strong @Mutable Date> eventDate =
                        ctx.replicate(id.toString() + ":date", STRONG, Date.class, date.getTime());
                event = ctx.replicate(id.toString(), activityConsistencyLevel, eventImpl, id, this.user, eventDate, text);
            } else {
                event = ctx.replicate(id.toString(), activityConsistencyLevel, eventImpl, id, this.user, date, text);
            }
            event.ref().initSelf(event);

            if (!(boolean)group.ref().isUserInGroup(this.user))
                throw new IllegalArgumentException("can only post in groups you are a member of");

            group.ref().addPost(event);

            return Option.apply(event);
        }).get();
    }

    public void sharePostWithFriend(CassandraTransactionContextBinding tr,
                                    Ref<? extends IUser> friend, Ref<? extends IPost> post) {
        checkLogin();
        doTransaction(tr, ctx -> {
            if (((List<Ref<? extends IUser>>)this.user.ref().getFriends()).stream().noneMatch(x -> Util.equalsUser(x, friend)))
                throw new IllegalArgumentException("target is not friend of user");
            friend.ref().addPost(post);
            return Option.apply(0);
        });
    }

    public void sendFriendRequest(CassandraTransactionContextBinding tr,
                                  Ref<? extends IUser> receiver) {
        checkLogin();
        doTransaction(tr, ctx -> {
            receiver.ref().addReceivedFriendRequest(this.user);
            this.user.ref().addSentFriendRequest(receiver);
            return Option.apply(0);
        });
    }

    public boolean acceptFriendRequest(CassandraTransactionContextBinding tr, int requestIndex) {
        checkLogin();
        return doTransaction(tr, ctx -> {
            List<Ref<? extends IUser>> requests = this.user.ref().getReceivedFriendRequests();
            if (requestIndex >= requests.size()) {
                return Option.apply(false);
            }

            Ref<? extends IUser> sender = requests.get(requestIndex);
            Util.acceptFriendRequest(this.user, sender);

            return Option.apply(true);
        }).get();
    }

    public void follow(CassandraTransactionContextBinding tr, Ref<? extends IUser> target) {
        checkLogin();
        doTransaction(tr, ctx -> {
            target.ref().addFollower(this.user);
            this.user.ref().addFollowing(target);
            return Option.apply(0);
        });
    }

    private void checkLogin() {
        if (this.user == null) {
            throw new IllegalStateException("no user is logged in for this session");
        }
    }
}
