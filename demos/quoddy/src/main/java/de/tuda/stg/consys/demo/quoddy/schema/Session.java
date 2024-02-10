package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.demo.quoddy.schema.datacentric.BoolBox;
import de.tuda.stg.consys.demo.quoddy.schema.datacentric.RefList;
import de.tuda.stg.consys.demo.quoddy.schema.datacentric.RefMap;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.logging.Logger;
import scala.Function1;
import scala.Option;

import java.io.Serializable;
import java.util.Date;
import java.util.List;
import java.util.Random;
import java.util.UUID;
import java.util.concurrent.TimeoutException;


@SuppressWarnings({"consistency"})
public class Session<SStore extends de.tuda.stg.consys.core.store.Store> {
    public ConsistencyLevel<SStore> userConsistencyLevel;
    public ConsistencyLevel<SStore> groupConsistencyLevel;
    public ConsistencyLevel<SStore> statusUpdateConsistencyLevel;
    public ConsistencyLevel<SStore> eventConsistencyLevel;
    public ConsistencyLevel<SStore> internalConsistencyLevel;

    public static Class<? extends IGroup> groupImpl;
    public static Class<? extends IUser> userImpl;
    public static Class<? extends IStatusUpdate> statusUpdateImpl;
    public static Class<? extends IEvent> eventImpl;
    public static int nMaxRetries;
    public static int retryDelay;

    public static boolean dataCentric;

    private final Store<String, Serializable, ConsistencyLevel<SStore>, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>> store;
    private Ref<? extends IUser> user;

    private final Random random = new Random();

    public Session(
            Store<String, Serializable, ConsistencyLevel<SStore>, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>> store,
            ConsistencyLevel<SStore> userConsistencyLevel,
            ConsistencyLevel<SStore> groupConsistencyLevel,
            ConsistencyLevel<SStore> statusUpdateConsistencyLevel,
            ConsistencyLevel<SStore> eventConsistencyLevel,
            ConsistencyLevel<SStore> internalConsistencyLevel) {
        this.store = store;
        this.userConsistencyLevel = userConsistencyLevel;
        this.groupConsistencyLevel = groupConsistencyLevel;
        this.statusUpdateConsistencyLevel = statusUpdateConsistencyLevel;
        this.eventConsistencyLevel = eventConsistencyLevel;
        this.internalConsistencyLevel = internalConsistencyLevel;
    }

    private <U> Option<U> doTransaction(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> transaction,
            Function1<TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Option<U>> code) {
        return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
    }

    private <U> Option<U> doTransactionWithRetries(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> transaction,
            Function1<TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Option<U>> code) {
        int nTries = 0;
        while (true) {
            try {
                return transaction == null ? store.transaction(code::apply) : code.apply(transaction);
            } catch (Exception e) {
                if (!(e instanceof TimeoutException)) throw e;
                Logger.warn("Timeout during operation. Retrying...");
                nTries++;
                try { Thread.sleep(random.nextInt(retryDelay)); } catch (InterruptedException ignored) {}
                if (nTries > nMaxRetries) {
                    Logger.err("Timeout during operation. Max retries reached.");
                    throw e;
                }
            }
        }
    }

    public Ref<? extends IUser> getUser() {
        return user;
    }

    @SuppressWarnings("unchecked")
    public Ref<? extends IUser> registerUser(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            String id, String name) {
        if (dataCentric) {
            this.user = doTransaction(tr, ctx -> {
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> friends =
                        ctx.replicate(id + ":friends", internalConsistencyLevel, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> followers =
                        ctx.replicate(id + ":followers", internalConsistencyLevel, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> following =
                        ctx.replicate(id + ":following", internalConsistencyLevel, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefList<Ref<? extends IGroup>>> groups =
                        ctx.replicate(id + ":groups", internalConsistencyLevel, (Class<RefList<Ref<? extends IGroup>>>)(Class)RefList.class);
                return Option.apply(ctx.replicate(id, userConsistencyLevel, userImpl, id, name, friends, followers, following, groups));
            }).get();
        } else {
            this.user = doTransaction(tr,
                    ctx -> Option.apply(ctx.replicate(id, userConsistencyLevel, userImpl, id, name))).get();
        }
        return this.user;
    }

    public Option<Ref<? extends IUser>> lookupUser(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            String id) {
        return doTransaction(tr, ctx -> Option.apply(ctx.lookup(id, userConsistencyLevel, userImpl)));
    }

    @SuppressWarnings("unchecked")
    public Ref<? extends IGroup> createGroup(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            String id, String name, String description, boolean requiresJoinConfirmation) {
        checkLogin();
        return doTransaction(tr, ctx -> {
            Ref<? extends IGroup> group;
            if (dataCentric) {
                Ref<@Strong @Mutable BoolBox> requires =
                        ctx.replicate(id + ":requires", internalConsistencyLevel, BoolBox.class, requiresJoinConfirmation);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> owners =
                        ctx.replicate(id + ":owners", internalConsistencyLevel, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> members =
                        ctx.replicate(id + ":members", internalConsistencyLevel, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
                Ref<@Strong @Mutable RefMap<UUID, Ref<? extends IUser>>> pending =
                        ctx.replicate(id + ":pending", internalConsistencyLevel, (Class<RefMap<UUID, Ref<? extends IUser>>>)(Class)RefMap.class);
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

    public Option<Ref<? extends IGroup>> lookupGroup(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            String id) {
        return doTransaction(tr, ctx -> Option.apply(ctx.lookup(id, groupConsistencyLevel, groupImpl)));
    }

    public void joinGroup(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            Ref<? extends IGroup> group) {
        checkLogin();
        doTransactionWithRetries(null, ctx -> {
            group.ref().join(user);
            user.ref().addParticipatingGroup(group);
            return Option.apply(0);
        });
    }

    public void postStatusToProfile(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            String text) {
        checkLogin();
        var id = UUID.randomUUID();

        doTransactionWithRetries(tr, ctx -> {
            Ref<? extends IStatusUpdate> status =
                    ctx.replicate(id.toString(), statusUpdateConsistencyLevel, statusUpdateImpl, id, this.user, text);

            this.user.ref().addPost(status);
            for (Ref<? extends IUser> follower : user.ref().getFollowers()) {
                follower.ref().addPost(status); // TODO: could lead to batch too large
            }
            // cyclic dependency for all-strong case: if two friends post simultaneously, they end up waiting for each
            // other's locks here
            for (Ref<? extends IUser> friend : user.ref().getFriends()) {
                friend.ref().addPost(status); // TODO: could lead to batch too large
            }

            return Option.apply(0);
        });
    }

    public void postStatusToGroup(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            String text, Ref<? extends IGroup> group) {
        checkLogin();
        var id = UUID.randomUUID();

        doTransactionWithRetries(tr, ctx -> {
            Ref<? extends IStatusUpdate> status =
                    ctx.replicate(id.toString(), statusUpdateConsistencyLevel, statusUpdateImpl, id, this.user, text);

            // potential deadlock for strong cases
            if (!(boolean)group.ref().isUserInGroup(this.user))
                throw new AppException("can only post in groups you are a member of");

            group.ref().addPost(status);

            return Option.apply(0);
        });
    }

    public Ref<? extends IEvent> postEventToGroup(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            String text, Date date, Ref<? extends IGroup> group) {
        checkLogin();
        var id = UUID.randomUUID();

        return doTransactionWithRetries(tr, ctx -> {
            Ref<? extends IEvent> event;
            if (dataCentric) {
                Ref<@Strong @Mutable Date> eventDate =
                        ctx.replicate(id + ":date", internalConsistencyLevel, Date.class, date.getTime());
                event = ctx.replicate(id.toString(), eventConsistencyLevel, eventImpl, id, this.user, eventDate, text);
            } else {
                event = ctx.replicate(id.toString(), eventConsistencyLevel, eventImpl, id, this.user, date, text);
            }
            event.ref().initSelf(event);

            // potential deadlock for strong cases
            if (!(boolean)group.ref().isUserInGroup(this.user))
                throw new AppException("can only post in groups you are a member of");

            group.ref().addPost(event);

            return Option.apply(event);
        }).get();
    }

    public void sharePostWithFriend(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            Ref<? extends IUser> friend, Ref<? extends IPost> post) {
        checkLogin();
        doTransactionWithRetries(tr, ctx -> {
            // potential deadlock for strong cases
            if (((List<Ref<? extends IUser>>)this.user.ref().getFriends()).stream().noneMatch(x -> Util.equalsUser(x, friend)))
                throw new AppException("target is not friend of user");
            friend.ref().addPost(post);
            return Option.apply(0);
        });
    }

    public void sendFriendRequest(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            Ref<? extends IUser> receiver) {
        checkLogin();
        doTransactionWithRetries(tr, ctx -> {
            // potential deadlock for strong cases
            receiver.ref().addReceivedFriendRequest(this.user);
            this.user.ref().addSentFriendRequest(receiver);
            Util.acceptFriendRequest(receiver, this.user);
            return Option.apply(0);
        });
    }

    public boolean acceptFriendRequest(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            int requestIndex) {
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

    public void follow(
            TransactionContext<String, Serializable, ConsistencyLevel<SStore>> tr,
            Ref<? extends IUser> target) {
        checkLogin();
        doTransactionWithRetries(tr, ctx -> {
            // potential deadlock for strong cases
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
