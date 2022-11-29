package de.tuda.stg.consys.demo;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

public class DemoUtils {
    private static final Random random = new Random();

    public static final List<String> WORDS = new ArrayList<>(Arrays.asList("small batch", "Etsy", "axe", "plaid", "McSweeney's", "VHS",
            "viral", "cliche", "post-ironic", "health", "goth", "literally", "Austin",
            "brunch", "authentic", "hella", "street art", "Tumblr", "Blue Bottle", "readymade",
            "occupy", "irony", "slow-carb", "heirloom", "YOLO", "tofu", "ethical", "tattooed",
            "vinyl", "artisan", "kale", "selfie"));

    public static final List<String> FIRST_NAMES = new ArrayList<>(Arrays.asList("Arthur", "Ford", "Tricia", "Zaphod"));

    public static final List<String> LAST_NAMES = new ArrayList<>(Arrays.asList("Dent", "Prefect", "McMillan", "Beeblebrox"));

    public static String addr(String identifier, int objectIndex, int replicaIndex) {
        return identifier + "$" + objectIndex + "$"+ replicaIndex;
    }

    public static String generateRandomName() {
        return FIRST_NAMES.get(random.nextInt(FIRST_NAMES.size()))
                + " " + LAST_NAMES.get(random.nextInt(LAST_NAMES.size()));
    }

    public static String generateRandomText(int nWords) {
        StringBuilder body = new StringBuilder(WORDS.get(random.nextInt(WORDS.size())));
        for (int i = 0; i < nWords - 1; i++)
            body.append(" ").append(WORDS.get(random.nextInt(WORDS.size())));
        return body.toString();
    }

    public static String generateRandomPassword() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < 12; i++) {
            sb.append((char)(random.nextInt('z' - 'a' + 1) + 'a'));
        }
        return sb.toString();
    }

    public static <E> E getRandomElement(List<E> list) {
        return list.get(random.nextInt(list.size()));
    }

    public static <E> E getRandomElementExcept(List<E> list, E object) {
        E element;
        do {
            element = list.get(random.nextInt(list.size()));
        } while (element == object);
        return element;
    }
}
