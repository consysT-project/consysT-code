package de.tuda.stg.consys.demo.quoddy;

import com.typesafe.config.Config;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.demo.quoddy.schema.Group;
import de.tuda.stg.consys.demo.quoddy.schema.User;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

import java.util.*;
import java.util.concurrent.TimeoutException;


public class QuoddyBenchmark extends CassandraDemoBenchmark {
    public static void main(String[] args) {
        start(QuoddyBenchmark.class, args);
    }

    private final int numOfUsersPerReplica;
    private final List<Session> sessions;
    private final List<Ref<User>> users;
    private final List<Ref<Group>> groups;

    private static final float maxPrice = 100;

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

    private static String addr(String identifier, int grpIndex, int replIndex) {
        return identifier + "$" + grpIndex + "$"+ replIndex;
    }

    private String generateRandomName() {
        return FIRST_NAMES.get(random.nextInt(FIRST_NAMES.size()))
                + " " + LAST_NAMES.get(random.nextInt(LAST_NAMES.size()));
    }

    private String generateRandomPassword() {
        return WORDS.get(random.nextInt(WORDS.size()));
    }

    private String generateRandomText(int n) {
        String body = WORDS.get(random.nextInt(WORDS.size()));
        for (int i = 0; i < n - 1; i++)
            body += " " + WORDS.get(random.nextInt(WORDS.size()));
        return body;
    }

    private Session randomLocalSession() {
        return sessions.get(random.nextInt(sessions.size()));
    }

    @Override
    public void setup() {
        System.out.println("Adding users");
        for (int grpIndex = 0; grpIndex < numOfUsersPerReplica; grpIndex++) {

            users.add(sessions.get(grpIndex).registerUser(
                    null, addr("user", grpIndex, processId()), generateRandomName()));

            groups.add(sessions.get(grpIndex).createGroup(
                    null, addr("user", grpIndex, processId()), generateRandomName(), generateRandomText(10), false));

            BenchmarkUtils.printProgress(grpIndex);
        }

        for (int grpIndex = 0; grpIndex < numOfUsersPerReplica; grpIndex++) {
            for (int replIndex = 0; replIndex < nReplicas(); replIndex++) {

            }
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
        sessions.clear();
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
            addFriend();
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

    }

    private void followUser() {

    }

    private void addFriend() {

    }
}
