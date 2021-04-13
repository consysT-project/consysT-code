package de.tuda.stg.consys.demo.eshop;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.eshop.schema.Database;
import de.tuda.stg.consys.demo.eshop.schema.ShoppingSite;
import de.tuda.stg.consys.demo.eshop.schema.User;
import de.tuda.stg.consys.japi.legacy.JRef;
import org.checkerframework.com.google.common.collect.Sets;
import scala.Option;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class EShopBenchmark extends DemoBenchmark {


	public static void main(String[] args) {
		start(EShopBenchmark.class, args);
	}

	private final int numOfProducts;
	private final int numOfUsers;


	public EShopBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
		super(config, outputResolver);

		numOfProducts = config.getInt("consys.bench.demo.eshop.products");
		numOfUsers = config.getInt("consys.bench.demo.eshop.users");


		EShopLevels.setWeak(getWeakLevel());
		EShopLevels.setStrong(getStrongLevel());
		EShopLevels.setCausal(getCausalLevel());
	}

	private JRef<Database> database;
	private JRef<ShoppingSite> shoppingSite;

	private final Random random = new Random();

	private static final String[] searchableWords = {"Alfa", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf",
		"Hotel", "India", "Juliett", "Kilo", "Lima", "Mike", "November", "Oscar", "Papa", "Quebec", "Romeo",
		"Sierra", "Tango", "Uniform", "Victor", "Whiskey", "Xray", "Yankee", "Zulu"};

	@Override
	public void setup() {
		if (processId() == 0) {
			database = system().replicate("db", new Database(100, 100), getWeakLevel());
			database.ref().init(numOfUsers, numOfProducts);
			shoppingSite = system().replicate("page", new ShoppingSite(database), getWeakLevel());

			List<String> initialProducts = new ArrayList<>(numOfProducts);
			for (int i = 0; i < numOfProducts; i++){
				String name = "ProductName" + i + searchableWords[random.nextInt(searchableWords.length)];
				double price =  (double) (100 + random.nextInt(99900)) / 100;
				//Add one random searchable word to the products
				initialProducts.add(name + ";" + price);
			}
			database.ref().addInitialProducts(initialProducts);

			for (int i = 0; i < numOfUsers; i++){
				String name = "User" + i;
				//Add one random searchable word to the products
				database.ref().addUser(name, Integer.toString(i));
				BenchmarkUtils.printProgress(i);
			}
			BenchmarkUtils.printDone();

			system().barrier("added");

			System.out.println("number of objects = " + system().numberOfObjects());

		} else {
			database = system().lookup("db", Database.class, getWeakLevel());
			shoppingSite = system().lookup("page", ShoppingSite.class, getWeakLevel());

			database.sync(); //Force dereference
			shoppingSite.sync();

			system().barrier("added");

			System.out.println("number of objects = " + system().numberOfObjects());

			database.sync();
			shoppingSite.sync();
		}
	}

	@Override
	public void operation() {
		if (processId() != 0) {
			randomTransaction();
		}
	}

	@Override
	public void cleanup() {
		System.out.println("number of objects = " + system().numberOfObjects());

		system().clear(Sets.newHashSet());
	}


	private void randomTransaction() {
		int roll = random.nextInt(100);

		//Zipf distribution
		if (roll < 38) {
			transactionSearch();
		} else if (roll < 57) {
			transactionViewInfo();
		} else if (roll < 70) {
			transactionAddCart();
		} else if (roll < 80) {
			transactionAddBalance();
		} else if (roll < 88) {
			transactionLogin();
		} else if (roll < 94) {
			transactionCheckout();
		} else if (roll < 100) {
			transactionLogout();
		}
	}

	private void transactionAddBalance() {
        System.out.println("--transactionAddBalance--");
	    shoppingSite.ref().addBalance((double) random.nextInt(100), false);
	    doSync(() -> {
	    	JRef<User> user = shoppingSite.ref().currentlyLoggedIn;
	    	if (user != null) user.sync();
		});
	}

	private void transactionAddCart() {
        System.out.println("--transactionAddCart--");
	    shoppingSite.ref().FromFoundAddToCart(random.nextInt(3) + 1, 1);
		doSync(() -> {
			JRef prod = shoppingSite.ref().foundProducts;
			if (prod != null) prod.sync();

			JRef ref = shoppingSite.ref().cartOfLoggedIn;
			if (ref != null) ref.sync();
		});
	}

	private void transactionCheckout() {
        System.out.println("--transactionCheckout--");
	    shoppingSite.ref().Checkout(false);

	    doSync(() -> {
			JRef ref = shoppingSite.ref().currentlyLoggedIn;
			if (ref != null) ref.sync();
		});
	}

	private void transactionLogin() {
        System.out.println("--transactionLogin--");
		int userIndex = random.nextInt(numOfUsers);
		shoppingSite.ref().login("User" + userIndex, Integer.toString(userIndex));

		doSync(() -> {
			JRef ref = shoppingSite.ref().currentlyLoggedIn;
			if (ref != null) ref.sync();
		});
	}

	private void transactionLogout() {
        System.out.println("--transactionLogout--");
	    shoppingSite.ref().Logout();
		doSync(() -> shoppingSite.sync());
	}

	private void transactionRegisterUser() {
		//TODO: This does not really work out...
		StringBuilder password = new StringBuilder();
		for(int j = 0; j < 6; j++){
			password.append((char) (random.nextInt(26) + 'a'));
		}
		password.append(random.nextInt(1000));

		byte[] usernameRaw = new byte[16];
		random.nextBytes(usernameRaw);

		shoppingSite.ref().RegisterNewUser("User" + new String(usernameRaw), password.toString());
		doSync(() -> {
			JRef ref = shoppingSite.ref().database;
			if (ref != null) ref.sync();
		});
	}

	private void transactionSearch() {
		shoppingSite.ref().Search(searchableWords[random.nextInt(searchableWords.length)], false, 1000);
		doSync(() -> {
			JRef ref = shoppingSite.ref().foundProducts;
			if (ref != null) ref.sync();
		});
	}

	private void transactionViewInfo() {
		shoppingSite.ref().FromFoundDisplayInfo(random.nextInt(3) + 1,false,false);
	}


}
