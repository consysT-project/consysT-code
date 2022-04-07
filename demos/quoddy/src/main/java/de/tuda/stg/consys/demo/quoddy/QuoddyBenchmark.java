package de.tuda.stg.consys.demo.quoddy;

import com.typesafe.config.Config;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.demo.quoddy.schema.*;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

import java.lang.reflect.InvocationTargetException;
import java.util.*;

@SuppressWarnings({"consistency"})
public class QuoddyBenchmark extends CassandraDemoBenchmark {
    public static void main(String[] args) {
        start(QuoddyBenchmark.class, args);
    }

    private final int numOfUsersPerReplica;
    private final int numOfGroupsPerReplica;

    private final List<Session> localSessions;
    private final List<Ref<User>> users;
    private final List<Ref<Group>> groups;
    private final List<Ref<Event>> events;

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
        super.setup();

        for (int i = 0; i < numOfUsersPerReplica; i++) {
            localSessions.add(new Session(store()));
        }

        System.out.println("Adding users");
        for (int usrIndex = 0; usrIndex < numOfUsersPerReplica; usrIndex++) {
            localSessions.get(usrIndex).registerUser(
                    null, addr("user", usrIndex, processId()), generateRandomName());
            BenchmarkUtils.printProgress(usrIndex);
        }

        System.out.println("Adding groups");
        for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
            Ref<Group> group = localSessions.get(grpIndex % numOfUsersPerReplica).createGroup(
                    null, addr("group", grpIndex, processId()), generateRandomName(),
                    generateRandomText(10), false);
            // every group starts with one post
            localSessions.get(grpIndex % numOfUsersPerReplica).postStatusToGroup(null, generateRandomText(20), group);
            // every group starts with one event
            Ref<Event> event = localSessions.get(grpIndex % numOfUsersPerReplica).
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
                    return Option.empty();
                });
            }

            BenchmarkUtils.printProgress(grpIndex);
        }

        barrier("users_added");

        for (int replIndex = 0; replIndex < nReplicas(); replIndex++) {
            for (int usrIndex = 0; usrIndex < numOfUsersPerReplica; usrIndex++) {
                users.add(localSessions.get(0).lookupUser(null, addr("user", usrIndex, replIndex)).get());
            }

            for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
                groups.add(localSessions.get(0).lookupGroup(null, addr("group", grpIndex, replIndex)).get());
            }
        }

        for (Session session : localSessions) {
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
        } catch (IllegalArgumentException e) {
            System.out.println(e.getMessage());
        } catch (Exception e) {
            if (e instanceof InvocationTargetException && ((InvocationTargetException)e).getTargetException() instanceof IllegalArgumentException) {
                System.out.println(e.getMessage());
            } else throw e;
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
            Ref<User> user = randomLocalSession().getUser();
            List<Ref<? extends Post>> feed = user.ref().getNewestPosts(5);
            for (Ref<? extends Post> post : feed) {
                post.ref().toString();
            }
            return Option.empty();
        });
    }

    private void readGroupFeed() {
        store().transaction(ctx -> {
            Ref<Group> group = getRandomElement(groups);
            List<Ref<? extends Post>> feed = group.ref().getNewestPosts(5);
            for (Ref<? extends Post> post : feed) {
                post.ref().toString();
            }
            return Option.empty();
        });
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

    private void joinGroup() {
        Session session = randomLocalSession();
        Ref<Group> group = getRandomElement(groups);
        store().transaction(ctx -> {
            session.joinGroup(ctx, group);
            return Option.empty();
        });
    }

    private void share() {
        Session session = randomLocalSession();
        Ref<User> user = session.getUser();
        store().transaction(ctx -> {
            Ref<Group> group = getRandomElement(user.ref().getParticipatingGroups());
            Ref<? extends Post> post = getRandomElement(group.ref().getNewestPosts(5));
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
            Ref<? extends Post> post = getRandomElement(group.ref().getNewestPosts(5));
            post.ref().addComment(new Comment(generateRandomText(10), user, new Date()));
            return Option.empty();
        });
    }

    private void commentOnFriendPost() {
        Session session = randomLocalSession();
        Ref<User> user = session.getUser();
        store().transaction(ctx -> {
            Ref<User> friend = getRandomElement(user.ref().getFriends());
            Ref<? extends Post> post = getRandomElement(friend.ref().getNewestPosts(5));
            post.ref().addComment(new Comment(generateRandomText(10), user, new Date()));
            return Option.empty();
        });
    }

    // TODO: model event updates with strong consistency?
    private void postEventUpdate() {
        Ref<Event> event = getRandomElement(events);
        store().transaction(ctx -> {
            event.ref().postUpdate(generateRandomText(10));
            return Option.empty();
        });
    }
}
