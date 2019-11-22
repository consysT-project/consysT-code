package de.tuda.stg.consys.demo.eshop;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.eshop.schema.Database;
import de.tuda.stg.consys.demo.eshop.schema.ShoppingSite;
import de.tuda.stg.consys.objects.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static de.tuda.stg.consys.demo.DemoUtils.printProgress;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class DistributedEShopBenchmark extends DemoBenchmark {


	public static void main(String[] args) {
		start(DistributedEShopBenchmark.class, args[0]);
	}

	private final int numOfTransactions;
	private final int numOfProducts;
	private final int numOfUsers;


	public DistributedEShopBenchmark(Config config) {
		super(config);
		numOfTransactions = config.getInt("consys.bench.demo.eshop.transactions");
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
			database = replicaSystem().replicate("db", new Database(100, 100), getWeakLevel());
			database.ref().init(numOfUsers, numOfProducts);
			shoppingSite = replicaSystem().replicate("page", new ShoppingSite(database), getWeakLevel());

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
				DemoUtils.printProgress(i);
			}
			DemoUtils.printDone();

			replicaSystem().barrier("added");

		} else {
			database = replicaSystem().lookup("db", Database.class, getWeakLevel());
			shoppingSite = replicaSystem().lookup("page", ShoppingSite.class, getWeakLevel());

			database.sync(); //Force dereference
			shoppingSite.sync();

			replicaSystem().barrier("added");

			database.sync();
			shoppingSite.sync();
		}
	}

	@Override
	public void iteration() {
		if (processId() != 0) {
			for (int i = 0; i < numOfTransactions; i++) {
				randomTransaction();
				printProgress(i);
			}
			DemoUtils.printDone();
		}
	}

	@Override
	public void cleanup() {
		replicaSystem().clear(Sets.newHashSet());
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
	}

	private void transactionAddCart() {
        System.out.println("--transactionAddCart--");
	    shoppingSite.ref().FromFoundAddToCart(random.nextInt(3) + 1, 1);
	}

	private void transactionCheckout() {
        System.out.println("--transactionCheckout--");
	    shoppingSite.ref().Checkout(false);
	}

	private void transactionLogin() {
        System.out.println("--transactionLogin--");
		int userIndex = random.nextInt(numOfUsers);
		shoppingSite.ref().login("User" + userIndex, Integer.toString(userIndex));
	}

	private void transactionLogout() {
        System.out.println("--transactionLogout--");
	    shoppingSite.ref().Logout();
	}

	private void transactionRegisterUser() {
		//TODO: This does not really work out...
		String password = "";
		for(int j = 0; j < 6; j++){
			password += (char) (random.nextInt(26) + 'a');
		}
		password += random.nextInt(1000);

		byte[] usernameRaw = new byte[16];
		random.nextBytes(usernameRaw);

		shoppingSite.ref().RegisterNewUser("User" + new String(usernameRaw), password);
	}

	private void transactionSearch() {
		shoppingSite.ref().Search(searchableWords[random.nextInt(searchableWords.length)], false, 1000);
	}

	private void transactionViewInfo() {
		shoppingSite.ref().FromFoundDisplayInfo(random.nextInt(3) + 1,false,false);
	}


}
