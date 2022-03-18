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
import java.util.concurrent.TimeoutException;


public class QuoddyBenchmark extends CassandraDemoBenchmark {
    public static void main(String[] args) {
        start(QuoddyBenchmark.class, args);
    }

    private final int numOfUsersPerReplica;
    private final int numOfGroupsPerReplica;

    private final List<Session> sessions;
    private final List<Ref<User>> users;
    private final List<Ref<Group>> groups;

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

        sessions = new LinkedList<>();
        for (int i = 0; i < numOfUsersPerReplica; i++) {
            sessions.add(new Session(store()));
        }

        users = new LinkedList<>();
        groups = new LinkedList<>();
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
        return sessions.get(random.nextInt(sessions.size()));
    }

    private <E> E getRandomElement(List<E> list) {
        return list.get(random.nextInt(list.size()));
    }

    private <E> E getRandomElementExcept(List<E> list, E object) {
        E element;
        do {
            element = list.get(random.nextInt(list.size()));
        } while (element == object);
        return element;
    }

    @Override
    public void setup() {
        System.out.println("Adding users");
        for (int usrIndex = 0; usrIndex < numOfUsersPerReplica; usrIndex++) {
            sessions.get(usrIndex).registerUser(
                    null, addr("user", usrIndex, processId()), generateRandomName());
            BenchmarkUtils.printProgress(usrIndex);
        }

        System.out.println("Adding groups");
        for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
            Ref<Group> group = sessions.get(grpIndex % numOfUsersPerReplica).createGroup(
                    null, addr("group", grpIndex, processId()), generateRandomName(),
                    generateRandomText(10), false);
            // every group starts with one post
            sessions.get(grpIndex % numOfUsersPerReplica).postStatusToGroup(null, generateRandomText(20), group);
            BenchmarkUtils.printProgress(grpIndex);
        }

        for (int replIndex = 0; replIndex < nReplicas(); replIndex++) {
            for (int usrIndex = 0; usrIndex < numOfUsersPerReplica; usrIndex++) {
                users.add(sessions.get(0).lookupUser(null, addr("user", usrIndex, replIndex)).get());
            }

            for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
                groups.add(sessions.get(0).lookupGroup(null, addr("group", grpIndex, replIndex)).get());
            }
        }

        for (Session session : sessions) {
            // every user starts as a member of one group
            session.joinGroup(null, getRandomElement(groups));
            // every user starts with one friend
            Ref<User> friend = getRandomElementExcept(users, session.getUser());
            session.sendFriendRequest(null, friend);
            store().transaction(ctx -> {
                Util.acceptFriendRequest(friend, session.getUser());
                return Option.empty();
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
        } catch (TimeoutException ignored) {

        }
    }

    @Override
    public void cleanup() {
        //system().clear(Sets.newHashSet());
        users.clear();
        groups.clear();

        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    @Transactional
    private void randomTransaction() throws TimeoutException {
        // TODO
        int rand = random.nextInt(100);
        if (rand < 12) {
            share();
        } else if (rand < 58) {
            followUser();
        } else if (rand < 80) {
            postStatusToGroup();
        } else if (rand < 100) {
            postStatusToProfile();
        } else {
            throw new IllegalStateException("cannot be here");
        }
    }

    private void postStatusToProfile() {
        randomLocalSession().postStatusToProfile(null, generateRandomText(20));
    }

    private void postStatusToGroup() {
        Session session = randomLocalSession();
        store().transaction(ctx -> {
            List<Ref<Group>> groups = session.getUser().ref().getParticipatingGroups();
            session.postStatusToGroup(ctx, generateRandomText(20), getRandomElement(groups));
            return Option.empty();
        });
    }

    private void followUser() {
        Session session = randomLocalSession();
        Ref<User> target = getRandomElement(users);
        store().transaction(ctx -> {
            session.follow(ctx, target);
            return Option.empty();
        });
    }

    // also immediately accepts friend request
    private void addFriend() {
        Session session = randomLocalSession();
        Ref<User> target = getRandomElement(users);
        store().transaction(ctx -> {
            session.sendFriendRequest(ctx, target);
            Util.acceptFriendRequest(target, session.getUser());
            return Option.empty();
        });
    }

    private void share() {
        Session session = randomLocalSession();
        Ref<User> user = session.getUser();
        store().transaction(ctx -> {
            Ref<Group> group = getRandomElement(user.ref().getParticipatingGroups());
            Ref<? extends Post> post = getRandomElement(group.ref().getFeed());
            Ref<User> friend = getRandomElement(user.ref().getFriends());
            session.sharePostWithFriend(ctx, friend, post);
            return Option.empty();
        });
    }

    private void commentOnGroupPost() {
        Session session = randomLocalSession();
        store().transaction(ctx -> {
            Ref<User> user = session.getUser();
            Ref<Group> group = getRandomElement(user.ref().getParticipatingGroups());
            Ref<? extends Post> post = getRandomElement(group.ref().getFeed());
            post.ref().addComment(new Comment(generateRandomText(10), user, new Date()));
            return Option.empty();
        });
    }

    private void commentOnFriendPost() {
        Session session = randomLocalSession();
        Ref<User> user = session.getUser();
        store().transaction(ctx -> {
            Ref<Group> group = getRandomElement(user.ref().getParticipatingGroups());
            Ref<? extends Post> post = getRandomElement(group.ref().getFeed());
            Ref<User> friend = getRandomElement(user.ref().getFriends());
            post.ref().addComment(new Comment(generateRandomText(10), user, new Date()));
            return Option.empty();
        });
    }
}
