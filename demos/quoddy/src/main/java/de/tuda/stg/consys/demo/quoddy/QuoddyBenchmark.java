package de.tuda.stg.consys.demo.quoddy;

import com.typesafe.config.Config;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.demo.quoddy.schema.*;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

import java.util.*;

@SuppressWarnings({"consistency"})
public class QuoddyBenchmark extends CassandraDemoBenchmark {
    public static void main(String[] args) {
        start(QuoddyBenchmark.class, args);
    }

    private final int numOfUsersPerReplica;
    private final int numOfGroupsPerReplica;

    private final List<Session> localSessions;
    private final List<Ref<? extends IUser>> users;
    private final List<Ref<? extends IGroup>> groups;
    private final List<Ref<? extends IEvent>> events;

    private static final List<String> WORDS = new ArrayList<>(Arrays.asList("small batch", "Etsy", "axe", "plaid", "McSweeney's", "VHS",
            "viral", "cliche", "post-ironic", "health", "goth", "literally", "Austin",
            "brunch", "authentic", "hella", "street art", "Tumblr", "Blue Bottle", "readymade",
            "occupy", "irony", "slow-carb", "heirloom", "YOLO", "tofu", "ethical", "tattooed",
            "vinyl", "artisan", "kale", "selfie"));
    private static final List<String> FIRST_NAMES = new ArrayList<>(Arrays.asList("Arthur", "Ford", "Tricia", "Zaphod"));
    private static final List<String> LAST_NAMES = new ArrayList<>(Arrays.asList("Dent", "Prefect", "McMillan", "Beeblebrox"));

    private final Random random = new Random();

    public QuoddyBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver);

        numOfUsersPerReplica = config.getInt("consys.bench.demo.quoddy.users");
        numOfGroupsPerReplica = config.getInt("consys.bench.demo.quoddy.groups");

        Session.userConsistencyLevel = getStrongLevel();
        Session.groupConsistencyLevel = getStrongLevel();
        Session.activityConsistencyLevel = getWeakLevel();

        localSessions = new ArrayList<>();
        users = new ArrayList<>();
        groups = new ArrayList<>();
        events = new ArrayList<>();
    }

    private static String addr(String identifier, int objectIndex, int replicaIndex) {
        return identifier + "$" + objectIndex + "$"+ replicaIndex;
    }

    private String generateRandomName() {
        return FIRST_NAMES.get(random.nextInt(FIRST_NAMES.size()))
                + " " + LAST_NAMES.get(random.nextInt(LAST_NAMES.size()));
    }

    private String generateRandomText(int n) {
        StringBuilder body = new StringBuilder(WORDS.get(random.nextInt(WORDS.size())));
        for (int i = 0; i < n - 1; i++)
            body.append(" ").append(WORDS.get(random.nextInt(WORDS.size())));
        return body.toString();
    }

    private Session randomLocalSession() {
        return localSessions.get(random.nextInt(localSessions.size()));
    }

    @Override
    public String getName() {
        return "QuoddyBenchmark";
    }

    @Override
    public void setup() {
        super.setup();

        Session.dataCentric = getBenchType() == BenchmarkType.MIXED;
        if (getBenchType() == BenchmarkType.MIXED) {
            Session.userImpl = de.tuda.stg.consys.demo.quoddy.schema.datacentric.User.class;
            Session.groupImpl = de.tuda.stg.consys.demo.quoddy.schema.datacentric.Group.class;
            Session.statusUpdateImpl = de.tuda.stg.consys.demo.quoddy.schema.datacentric.StatusUpdate.class;
            Session.eventImpl = de.tuda.stg.consys.demo.quoddy.schema.datacentric.Event.class;
        } else {
            Session.userImpl = de.tuda.stg.consys.demo.quoddy.schema.opcentric.User.class;
            Session.groupImpl = de.tuda.stg.consys.demo.quoddy.schema.opcentric.Group.class;
            Session.statusUpdateImpl = de.tuda.stg.consys.demo.quoddy.schema.opcentric.StatusUpdate.class;
            Session.eventImpl = de.tuda.stg.consys.demo.quoddy.schema.opcentric.Event.class;
        }

        for (int i = 0; i < numOfUsersPerReplica; i++) {
            localSessions.add(new Session(store()));
        }

        System.out.println("Adding users and groups");
        for (int usrIndex = 0; usrIndex < numOfUsersPerReplica; usrIndex++) {
            localSessions.get(usrIndex).registerUser(
                    null, addr("user", usrIndex, processId()), generateRandomName());
            BenchmarkUtils.printProgress(usrIndex);
        }

        for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
            Ref<? extends IGroup> group = localSessions.get(grpIndex % numOfUsersPerReplica).createGroup(
                    null, addr("group", grpIndex, processId()), generateRandomName(),
                    generateRandomText(10), false);
            // every group starts with one post
            localSessions.get(grpIndex % numOfUsersPerReplica).postStatusToGroup(null, generateRandomText(20), group);
            // every group starts with one event
            Ref<? extends IEvent> event = localSessions.get(grpIndex % numOfUsersPerReplica).
                    postEventToGroup(null, generateRandomText(20), new Date(), group);
            events.add(event);

            try {
                Thread.sleep(50);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }

            // every event has some subscribers
            for (int i = 0; i < 5; i++) {
                store().transaction(ctx -> {
                    event.ref().addSubscriber(getRandomElement(localSessions).getUser());
                    return Option.apply(0);
                });
            }

            BenchmarkUtils.printProgress(grpIndex);
        }

        barrier("users_added");

        System.out.println("Getting users and items from other replicas");
        for (int replIndex = 0; replIndex < nReplicas(); replIndex++) {
            for (int usrIndex = 0; usrIndex < numOfUsersPerReplica; usrIndex++) {
                users.add(localSessions.get(0).lookupUser(null, addr("user", usrIndex, replIndex)).get());
            }

            for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
                groups.add(localSessions.get(0).lookupGroup(null, addr("group", grpIndex, replIndex)).get());
            }
        }

        System.out.println("Setting up initial configuration");
        for (Session session : localSessions) {
            // every user starts as a member of one group
            session.joinGroup(null, getRandomElement(groups));
            // every user starts with one friend
            Ref<? extends IUser> friend = getRandomElementExcept(users, session.getUser());
            session.sendFriendRequest(null, friend);
            store().transaction(ctx -> {
                Util.acceptFriendRequest(friend, session.getUser());
                return Option.apply(0);
            });
            // every user starts with one post
            session.postStatusToProfile(null, generateRandomText(20));
        }

        BenchmarkUtils.printDone();
    }

    @Override
    public void operation() {
        try {
            randomTransaction();
        } catch (IllegalArgumentException e) {
            System.out.println(e.getMessage());
            throw e;
        }
    }

    @Override
    public void cleanup() {
        super.cleanup();
        localSessions.clear();
        users.clear();
        groups.clear();
        events.clear();

        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    @Transactional
    private void randomTransaction() {
        int rand = random.nextInt(100);
        if (rand < 33) {
            // 33%
            readPersonalFeed();
        } else if (rand < 50) {
            // 17%
            readGroupFeed();
        } else if (rand < 61) {
            // 11%
            postStatusToProfile();
        } else if (rand < 69) {
            // 8%
            postStatusToGroup();
        } else if (rand < 76) {
            // 7%
            followUser();
        } else if (rand < 82) {
            // 6%
            addFriend();
        } else if (rand < 87) {
            // 5%
            share();
        } else if (rand < 91) {
            // 4%
            commentOnFriendPost();
        } else if (rand < 95) {
            // 4%
            commentOnGroupPost();
        } else if (rand < 98) {
            // 3%
            joinGroup();
        } else {
            // 3%
            postEventUpdate();
        }
    }

    private void readPersonalFeed() {
        // render feed, where the first few comments are shown
        store().transaction(ctx -> {
            Ref<? extends IUser> user = randomLocalSession().getUser();
            List<Ref<? extends IPost>> feed = user.ref().getNewestPosts(5);
            for (Ref<? extends IPost> post : feed) {
                post.ref().toString();
            }
            return Option.apply(0);
        });
    }

    private void readGroupFeed() {
        store().transaction(ctx -> {
            Ref<? extends IGroup> group = getRandomElement(groups);
            List<Ref<? extends IPost>> feed = group.ref().getNewestPosts(5);
            for (Ref<? extends IPost> post : feed) {
                post.ref().toString();
            }
            return Option.apply(0);
        });
    }

    private void postStatusToProfile() {
        randomLocalSession().postStatusToProfile(null, generateRandomText(20));
    }

    private void postStatusToGroup() {
        Session session = randomLocalSession();
        store().transaction(ctx -> {
            List<Ref<? extends IGroup>> groups = session.getUser().ref().getParticipatingGroups();
            session.postStatusToGroup(ctx, generateRandomText(20), getRandomElement(groups));
            return Option.apply(0);
        });
    }

    private void followUser() {
        Session session = randomLocalSession();
        Ref<? extends IUser> target = getRandomElement(users);
        store().transaction(ctx -> {
            session.follow(ctx, target);
            return Option.apply(0);
        });
    }

    // also immediately accepts friend request
    private void addFriend() {
        Session session = randomLocalSession();
        Ref<? extends IUser> target = getRandomElement(users);
        store().transaction(ctx -> {
            session.sendFriendRequest(ctx, target);
            Util.acceptFriendRequest(target, session.getUser());
            return Option.apply(0);
        });
    }

    private void joinGroup() {
        Session session = randomLocalSession();
        Ref<? extends IGroup> group = getRandomElement(groups);
        store().transaction(ctx -> {
            session.joinGroup(ctx, group);
            return Option.apply(0);
        });
    }

    private void share() {
        Session session = randomLocalSession();
        Ref<? extends IUser> user = session.getUser();
        store().transaction(ctx -> {
            Ref<? extends IGroup> group = getRandomElement(user.ref().getParticipatingGroups());
            Ref<? extends IPost> post = getRandomElement(group.ref().getNewestPosts(5));
            Ref<? extends IUser> friend = getRandomElement(user.ref().getFriends());
            session.sharePostWithFriend(ctx, friend, post);
            return Option.apply(0);
        });
    }

    private void commentOnGroupPost() {
        Session session = randomLocalSession();
        store().transaction(ctx -> {
            Ref<? extends IUser> user = session.getUser();
            Ref<? extends IGroup> group = getRandomElement(user.ref().getParticipatingGroups());
            Ref<? extends IPost> post = getRandomElement(group.ref().getNewestPosts(5));
            post.ref().addComment(new Comment(generateRandomText(10), user, new Date()));
            return Option.apply(0);
        });
    }

    private void commentOnFriendPost() {
        Session session = randomLocalSession();
        Ref<? extends IUser> user = session.getUser();
        store().transaction(ctx -> {
            Ref<? extends IUser> friend = getRandomElement(user.ref().getFriends());
            Ref<? extends IPost> post = getRandomElement(friend.ref().getNewestPosts(5));
            post.ref().addComment(new Comment(generateRandomText(10), user, new Date()));
            return Option.apply(0);
        });
    }

    // TODO: model event updates with strong consistency?
    private void postEventUpdate() {
        Ref<? extends IEvent> event = getRandomElement(events);
        store().transaction(ctx -> {
            event.ref().postUpdate(generateRandomText(10));
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
    public void test() {
        if (processId() != 0) return;
        System.out.println("## TEST ##");

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

        System.out.println("## TEST SUCCESS ##");
    }
}
