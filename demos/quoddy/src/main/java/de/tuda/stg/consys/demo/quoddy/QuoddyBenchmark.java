package de.tuda.stg.consys.demo.quoddy;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.quoddy.schema.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.logging.Logger;
import scala.Option;

import java.util.*;

@SuppressWarnings({"consistency"})
public class QuoddyBenchmark extends DemoRunnable {
    public static void main(String[] args) {
        JBenchExecution.execute("quoddy", QuoddyBenchmark.class, args);
    }

    private final int numOfUsersPerReplica;
    private final int numOfGroupsPerReplica;

    private final List<Session> localSessions;
    private final List<Ref<? extends IUser>> users;
    private final List<Ref<? extends IGroup>> groups;
    private final List<Ref<? extends IEvent>> events;

    public QuoddyBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);
        localSessions = new ArrayList<>();
        users = new ArrayList<>();
        groups = new ArrayList<>();
        events = new ArrayList<>();

        numOfUsersPerReplica = config.toConfig().getInt("consys.bench.demo.quoddy.users");
        numOfGroupsPerReplica = config.toConfig().getInt("consys.bench.demo.quoddy.groups");

        Session.nMaxRetries = config.toConfig().getInt("consys.bench.demo.quoddy.retries");
        Session.retryDelay = config.toConfig().getInt("consys.bench.demo.quoddy.retryDelay");

        Session.internalConsistencyLevel = getStrongLevel();
        Session.userConsistencyLevel = getLevelWithMixedFallback(getWeakLevel());
        Session.groupConsistencyLevel = getLevelWithMixedFallback(getWeakLevel());
        Session.activityConsistencyLevel = getLevelWithMixedFallback(getWeakLevel());

        if (benchType == BenchmarkType.MIXED) {
            Session.dataCentric = true;
            Session.userImpl = de.tuda.stg.consys.demo.quoddy.schema.datacentric.User.class;
            Session.groupImpl = de.tuda.stg.consys.demo.quoddy.schema.datacentric.Group.class;
            Session.statusUpdateImpl = de.tuda.stg.consys.demo.quoddy.schema.datacentric.StatusUpdate.class;
            Session.eventImpl = de.tuda.stg.consys.demo.quoddy.schema.datacentric.Event.class;
        } else {
            Session.dataCentric = false;
            Session.userImpl = de.tuda.stg.consys.demo.quoddy.schema.opcentric.User.class;
            Session.groupImpl = de.tuda.stg.consys.demo.quoddy.schema.opcentric.Group.class;
            Session.statusUpdateImpl = de.tuda.stg.consys.demo.quoddy.schema.opcentric.StatusUpdate.class;
            Session.eventImpl = de.tuda.stg.consys.demo.quoddy.schema.opcentric.Event.class;
        }
    }

    @Override
    public void setup() {
        for (int i = 0; i < numOfUsersPerReplica; i++) {
            localSessions.add(new Session(store()));
        }

        Logger.debug(procName(), "Creating objects");
        for (int usrIndex = 0; usrIndex < numOfUsersPerReplica; usrIndex++) {
            localSessions.get(usrIndex).registerUser(
                    null, DemoUtils.addr("user", usrIndex, processId()), DemoUtils.generateRandomName());
            BenchmarkUtils.printProgress(usrIndex);
        }

        for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
            Ref<? extends IGroup> group = localSessions.get(grpIndex % numOfUsersPerReplica).createGroup(
                    null, DemoUtils.addr("group", grpIndex, processId()), DemoUtils.generateRandomName(),
                    DemoUtils.generateRandomText(10), false);
            // every group starts with one post
            localSessions.get(grpIndex % numOfUsersPerReplica).postStatusToGroup(null, DemoUtils.generateRandomText(20), group);
            // every group starts with one event
            Ref<? extends IEvent> event = localSessions.get(grpIndex % numOfUsersPerReplica).
                    postEventToGroup(null, DemoUtils.generateRandomText(20), new Date(), group);
            events.add(event);

            // every event has some subscribers
            for (int i = 0; i < 5; i++) {
                store().transaction(ctx -> {
                    event.ref().addSubscriber(DemoUtils.getRandomElement(localSessions).getUser());
                    return Option.apply(0);
                });
            }

            BenchmarkUtils.printProgress(grpIndex);
        }

        barrier("users_added");

        Logger.debug(procName(), "Collecting objects");
        for (int replIndex = 0; replIndex < nReplicas; replIndex++) {
            for (int usrIndex = 0; usrIndex < numOfUsersPerReplica; usrIndex++) {
                users.add(localSessions.get(0).lookupUser(null, DemoUtils.addr("user", usrIndex, replIndex)).get());
            }

            for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
                groups.add(localSessions.get(0).lookupGroup(null, DemoUtils.addr("group", grpIndex, replIndex)).get());
            }
        }

        Logger.debug(procName(), "Setting up initial configuration");
        for (Session session : localSessions) {
            // every user starts as a member of one group
            session.joinGroup(null, DemoUtils.getRandomElement(groups));
            // every user starts with one friend
            Ref<? extends IUser> friend = DemoUtils.getRandomElementExcept(users, session.getUser());
            session.sendFriendRequest(null, friend);
            store().transaction(ctx -> {
                Util.acceptFriendRequest(friend, session.getUser());
                return Option.apply(0);
            });
            // every user starts with one post
            session.postStatusToProfile(null, DemoUtils.generateRandomText(20));
        }

        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        localSessions.clear();
        users.clear();
        groups.clear();
        events.clear();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                withExceptionHandling(this::readPersonalFeed),
                withExceptionHandling(this::readGroupFeed),
                withExceptionHandling(this::postStatusToProfile),
                withExceptionHandling(this::postStatusToGroup),
                withExceptionHandling(this::followUser),
                withExceptionHandling(this::addFriend),
                withExceptionHandling(this::share),
                withExceptionHandling(this::commentOnFriendPost),
                withExceptionHandling(this::commentOnGroupPost),
                withExceptionHandling(this::joinGroup),
                withExceptionHandling(this::postEventUpdate)
        });
    }

    private Runnable withExceptionHandling(Runnable op) {
        return () -> {
            try {
                op.run();
            } catch (AppException e) {
                System.err.println(e.getMessage());
            }
        };
    }

    private void readPersonalFeed() {
        // render feed, where the first few comments are shown
        store().transaction(ctx -> {
            Ref<? extends IUser> user = DemoUtils.getRandomElement(localSessions).getUser();
            List<Ref<? extends IPost>> feed = user.ref().getNewestPosts(5);
            for (Ref<? extends IPost> post : feed) {
                post.ref().toString();
            }
            return Option.apply(0);
        });
    }

    private void readGroupFeed() {
        store().transaction(ctx -> {
            Ref<? extends IGroup> group = DemoUtils.getRandomElement(groups);
            List<Ref<? extends IPost>> feed = group.ref().getNewestPosts(5);
            for (Ref<? extends IPost> post : feed) {
                post.ref().toString();
            }
            return Option.apply(0);
        });
    }

    private void postStatusToProfile() {
        DemoUtils.getRandomElement(localSessions).postStatusToProfile(null, DemoUtils.generateRandomText(20));
    }

    private void postStatusToGroup() {
        Session session = DemoUtils.getRandomElement(localSessions);
        store().transaction(ctx -> {
            List<Ref<? extends IGroup>> groups = session.getUser().ref().getParticipatingGroups();
            if (groups.isEmpty()) {
                // may happen in all-weak case
                System.err.println("participating groups was empty");
                return Option.empty();
            }
            session.postStatusToGroup(ctx, DemoUtils.generateRandomText(20), DemoUtils.getRandomElement(groups));
            return Option.apply(0);
        });
    }

    private void followUser() {
        Session session = DemoUtils.getRandomElement(localSessions);
        Ref<? extends IUser> target = DemoUtils.getRandomElement(users);
        store().transaction(ctx -> {
            session.follow(ctx, target);
            return Option.apply(0);
        });
    }

    private void addFriend() {
        // also immediately accepts friend request
        Session session = DemoUtils.getRandomElement(localSessions);
        Ref<? extends IUser> target = DemoUtils.getRandomElement(users);

        Option<TransactionResult> result = store().transaction(ctx -> {
            var trxResult = !isTestMode ? new TransactionResult() : new TransactionResult(
                    new UserState[] {
                            new UserState(session.getUser()),
                            new UserState(target) },
                    new GroupState[0]);

            session.sendFriendRequest(ctx, target);
            Util.acceptFriendRequest(target, session.getUser());

            return Option.apply(trxResult);
        });

        if (isTestMode && result.isDefined())
            addFriendTest(result.get());
    }

    private void addFriendTest(TransactionResult result) {
        store().transaction(ctx -> {
            var sender = result.users[0].ref;
            var target = result.users[1].ref;

            boolean isFriend1 = false;
            for (var f : sender.ref().getFriends())
                isFriend1 |= Util.equalsUser(f, target);
            boolean isFriend2 = false;
            for (var f : target.ref().getFriends())
                isFriend2 |= Util.equalsUser(f, sender);

            check("mutual friends after 'add friend'", isFriend1 && isFriend2);

            return Option.apply(0);
        });
    }

    private void joinGroup() {
        Session session = DemoUtils.getRandomElement(localSessions);
        Ref<? extends IGroup> group = DemoUtils.getRandomElement(groups);

        Option<TransactionResult> result = store().transaction(ctx -> {
            var trxResult = !isTestMode ? new TransactionResult() : new TransactionResult(
                    new UserState[] {
                            new UserState(session.getUser())},
                    new GroupState[] {
                            new GroupState(group)});

            session.joinGroup(ctx, group);

            return Option.apply(trxResult);
        });

        if (isTestMode && result.isDefined())
            joinGroupTest(result.get());
    }

    public void joinGroupTest(TransactionResult result) {
        store().transaction(ctx -> {
            var user = result.users[0].ref;
            var group = result.groups[0].ref;

            boolean isMember = false;
            for (var member : group.ref().getMembers())
                isMember |= Util.equalsUser(member, user);

            check("user is member after 'join'", isMember);

            return Option.empty();
        });
    }

    private void share() {
        Session session = DemoUtils.getRandomElement(localSessions);
        Ref<? extends IUser> user = session.getUser();
        store().transaction(ctx -> {
            var groups = user.ref().getParticipatingGroups();
            var friends = user.ref().getFriends();
            if (groups.isEmpty() || friends.isEmpty()) {
                // may happen in all-weak case
                System.err.println("friends or groups was empty");
                return Option.empty();
            }

            Ref<? extends IGroup> group = DemoUtils.getRandomElement(groups);
            Ref<? extends IPost> post = DemoUtils.getRandomElement(group.ref().getNewestPosts(5));
            Ref<? extends IUser> friend = DemoUtils.getRandomElement(friends);
            session.sharePostWithFriend(ctx, friend, post);
            return Option.apply(0);
        });
    }

    private void commentOnGroupPost() {
        Session session = DemoUtils.getRandomElement(localSessions);
        Ref<? extends IUser> user = session.getUser();
        store().transaction(ctx -> {
            var groups = user.ref().getParticipatingGroups();
            if (groups.isEmpty()) {
                // may happen in all-weak case
                System.err.println("groups was empty");
                return Option.empty();
            }

            Ref<? extends IGroup> group = DemoUtils.getRandomElement(user.ref().getParticipatingGroups());
            Ref<? extends IPost> post = DemoUtils.getRandomElement(group.ref().getNewestPosts(5));
            post.ref().addComment(new Comment(DemoUtils.generateRandomText(10), user, new Date()));
            return Option.apply(0);
        });
    }

    private void commentOnFriendPost() {
        Session session = DemoUtils.getRandomElement(localSessions);
        Ref<? extends IUser> user = session.getUser();
        store().transaction(ctx -> {
            var friends = user.ref().getFriends();
            if (groups.isEmpty()) {
                // may happen in all-weak case
                System.err.println("friends was empty");
                return Option.empty();
            }

            Ref<? extends IUser> friend = DemoUtils.getRandomElement(friends);
            Ref<? extends IPost> post = DemoUtils.getRandomElement(friend.ref().getNewestPosts(5));
            post.ref().addComment(new Comment(DemoUtils.generateRandomText(10), user, new Date()));
            return Option.apply(0);
        });
    }

    // TODO: model event updates with strong consistency?
    private void postEventUpdate() {
        Ref<? extends IEvent> event = DemoUtils.getRandomElement(events);
        store().transaction(ctx -> {
            event.ref().postUpdate(DemoUtils.generateRandomText(10));
            return Option.apply(0);
        });
    }

    /**
     * Checked invariants:
     *  - friends relation
     *  - group-member relation
     *  -
     *  -
     */
    @Override
    public void test() {
        if (processId() != 0) return;

        check("users non empty", !users.isEmpty());

        store().transaction(ctx -> {
            for (var user : users) {
                // check friendship relation
                check("friends non empty", !user.ref().getFriends().isEmpty());
                for (var friend : user.ref().getFriends()) {
                    boolean isMutualFriends = false;
                    for (var f : friend.ref().getFriends())
                        isMutualFriends |= Util.equalsUser(f, user);

                    check("users are mutual friends", isMutualFriends);
                }

                // check group membership relation
                check("groups non empty", !user.ref().getParticipatingGroups().isEmpty());
                for (var group : user.ref().getParticipatingGroups()) {
                    var members = group.ref().getMembers();
                    var owners = group.ref().getOwners();
                    members.addAll(owners);

                    boolean isMember = false;
                    for (var member : members)
                        isMember |= Util.equalsUser(member, user);

                    check("user is member of groups they are participating in", isMember);
                }
            }

            // check group membership relation
            for (var group : groups) {
                var members = group.ref().getMembers();
                var owners = group.ref().getOwners();
                members.addAll(owners);
                check("group has owner", !owners.isEmpty());

                for (var member : members) {
                    boolean isInGroup = false;
                    for (var pg : member.ref().getParticipatingGroups())
                        isInGroup |= group.ref().getId().equals(pg.ref().getId());

                    check("user participates in group they are a member of", isInGroup);
                }
            }

            return Option.apply(0);
        });

        printTestResult();
    }

    private static class TransactionResult {
        Exception[] appExceptions = new Exception[] {};
        UserState[] users = new UserState[] {};
        GroupState[] groups = new GroupState[] {};

        TransactionResult() {}

        TransactionResult(UserState[] users, GroupState[] groups) {
            this.users = users;
            this.groups = groups;
        }
    }

    private static class UserState {
        final Ref<? extends IUser> ref;

        UserState(Ref<? extends IUser> ref) {
            this.ref = ref;
        }
    }

    private static class GroupState {
        final Ref<? extends IGroup> ref;

        GroupState(Ref<? extends IGroup> ref) {
            this.ref = ref;
        }
    }
}
