package de.tuda.stg.consys.demo.quoddy;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.quoddy.schema.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Function1;
import scala.Option;

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
            Util.postStatusToPersonalProfile(this.user, status);
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
            Util.postStatusToGroup(group, status);
            return Option.empty();
        });
    }

    public void shareActivityWithFriend(CassandraTransactionContextBinding tr,
                                        Ref<User> friend, Ref<? extends Activity> activity) {
        checkLogin();
        doTransaction(tr, ctx -> {
            if (((List<Ref<User>>)this.user.ref().getFriends()).stream().noneMatch(x -> Util.equalsUser(x, friend)))
                throw new IllegalArgumentException("target is not friend of user");
            Util.shareActivity(friend, activity);
            return Option.empty();
        });
    }

    private void checkLogin() {
        if (this.user == null) {
            throw new IllegalStateException("no user is logged in for this session");
        }
    }
}
