package de.tuda.stg.consys.demo.rubis;

import com.typesafe.config.Config;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.demo.rubis.schema.AuctionStore;
import de.tuda.stg.consys.demo.rubis.schema.Category;
import de.tuda.stg.consys.demo.rubis.schema.Util;
import scala.Option;

import java.util.*;
import java.util.concurrent.TimeoutException;


public class RubisBenchmark extends CassandraDemoBenchmark {
    public static void main(String[] args) {
        start(RubisBenchmark.class, args);
    }

    private final int numOfUsersPerReplica;
    private final List<UserInterface> rubisInterfaces;
    private final List<UUID> localItems;
    private final List<UUID> allItems;

    private static final float maxPrice = 100;

    private static final List<String> WORDS = new ArrayList<>(Arrays.asList("small batch", "Etsy", "axe", "plaid", "McSweeney's", "VHS",
            "viral", "cliche", "post-ironic", "health", "goth", "literally", "Austin",
            "brunch", "authentic", "hella", "street art", "Tumblr", "Blue Bottle", "readymade",
            "occupy", "irony", "slow-carb", "heirloom", "YOLO", "tofu", "ethical", "tattooed",
            "vinyl", "artisan", "kale", "selfie"));
    private static final List<String> FIRST_NAMES = new ArrayList<>(Arrays.asList("Arthur", "Ford", "Tricia", "Zaphod"));
    private static final List<String> LAST_NAMES = new ArrayList<>(Arrays.asList("Dent", "Prefect", "McMillan", "Beeblebrox"));

    private final Random random = new Random();

    public RubisBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver);

        numOfUsersPerReplica = config.getInt("consys.bench.demo.rubis.users");

        UserInterface.userConsistencyLevel = getStrongLevel();
        UserInterface.itemConsistencyLevel = getStrongLevel();
        UserInterface.bidConsistencyLevel = getWeakLevel();
        UserInterface.storeConsistencyLevel = getStrongLevel();

        rubisInterfaces = new LinkedList<>();
        for (int i = 0; i < numOfUsersPerReplica; i++) {
            rubisInterfaces.add(new UserInterface(store()));
        }

        allItems = new LinkedList<>();
        localItems = new LinkedList<>();
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

    private Category getRandomCategory() {
        return Category.values()[random.nextInt(Category.values().length)];
    }

    private float getRandomPrice(float max) {
        return random.nextFloat() * max;
    }

    private UserInterface randomLocalUser() {
        return rubisInterfaces.get(random.nextInt(rubisInterfaces.size()));
    }

    private UUID randomItem() {
        return allItems.get(random.nextInt(allItems.size()));
    }

    @Override
    public void setup() {
        if (processId() == 0) {
            store().transaction(ctx -> {
                ctx.replicate(Util.auctionStoreKey, getStrongLevel(), AuctionStore.class);
                return Option.empty();
            });
        }

        System.out.println("Adding users");
        for (int grpIndex = 0; grpIndex < numOfUsersPerReplica; grpIndex++) {

            rubisInterfaces.get(grpIndex).registerUser(addr("user", grpIndex, processId()), generateRandomName(),
                    generateRandomPassword(), "mail@example.com");

            rubisInterfaces.get(grpIndex).addBalance(numOfUsersPerReplica * nReplicas() * maxPrice * 1.3f);

            rubisInterfaces.get(grpIndex).registerItem(generateRandomText(1), generateRandomText(10),
                    getRandomCategory(), getRandomPrice(maxPrice * 1.3f), 300);

            BenchmarkUtils.printProgress(grpIndex);
        }

        for (int grpIndex = 0; grpIndex < numOfUsersPerReplica; grpIndex++) {
            for (int replIndex = 0; replIndex < nReplicas(); replIndex++) {
                for (var cat : Category.values()) {
                    allItems.addAll(randomLocalUser().browseCategoryItems(cat));
                }
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
        rubisInterfaces.clear();
        localItems.clear();
        allItems.clear();

        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    @Transactional
    private void randomTransaction() throws TimeoutException {
        int rand = random.nextInt(100);
        if (rand < 12) /*12*/ {
            closeAuction();
        } else if (rand < 58) {
            buyNow();
        } else if (rand < 80) {
            placeBid();
        } else if (rand < 100) {
            browseCategory();
        } else {
            throw new IllegalStateException("cannot be here");
        }
    }

    private void placeBid() throws TimeoutException {
        UUID item = randomItem();
        UserInterface user = randomLocalUser();

        float bid = user.getTopBid(item)._2;
        user.placeBid(item, bid * (1 + random.nextFloat()));
    }

    private void buyNow() throws TimeoutException {
        UUID item = randomItem();
        UserInterface user = randomLocalUser();

        user.buyNow(item);
    }

    private void closeAuction() throws TimeoutException {
        int n = random.nextInt(rubisInterfaces.size());
        UserInterface user = rubisInterfaces.get(n);
        UUID item = localItems.get(n);

        user.endAuctionImmediately(item);
    }

    private void browseCategory() {
        Category category = getRandomCategory();
        UserInterface user = randomLocalUser();
        user.browseCategory(category);
    }
}
