package de.tuda.stg.consys.demo.messagegroups;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.bench.DistBenchmark;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.messagegroups.schema.Group;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class DistributedBenchmark extends DistBenchmark {


	public static void main(String[] args) {
		Config config = ConfigFactory.parseFile(new File("./resources/" + args[0]));
		DistBenchmark bench = new DistributedBenchmark(config);
		bench.runBenchmark();
	}

	private static final int NUM_OF_GROUPS = 1000;
	private static final int NUM_OF_TRANSACTIONS = 1000;

	private final List<JRef<@Strong Group>> groups = new ArrayList<>(NUM_OF_GROUPS * numOfReplicas());
	private final List<JRef<@Weak User>> users = new ArrayList<>(NUM_OF_GROUPS * numOfReplicas());

	private final Random random = new Random();


	public DistributedBenchmark(String configName) {
		super(configName);
	}

	public DistributedBenchmark(Config config) {
		super(config);
	}

	private static String name(String identifier, int grpIndex, int replIndex) {
		return identifier + "$" + grpIndex + "$"+ replIndex;
	}


	private int numOfReplicas() {
		return replicaSystem().numOfReplicas();
	}

	@Override
	public void setup() {
		System.out.println("Adding users");
		for (int grpIndex = 0; grpIndex <= NUM_OF_GROUPS; grpIndex++) {

			JRef<Group> group = replicaSystem().replicate
				(name("group", grpIndex, processId()), new Group(), JConsistencyLevels.STRONG);
			JRef<Inbox> inbox =  replicaSystem().replicate(
				name("inbox", grpIndex, processId()), new Inbox(), JConsistencyLevels.WEAK);
			JRef<User> user = replicaSystem().replicate(
				name("user", grpIndex, processId()), new User(inbox, name("alice", grpIndex, processId())), JConsistencyLevels.WEAK);


			group.ref().addUser(user);

			System.out.print(grpIndex % 100 == 0 ? grpIndex : ".");
		}

		for (int grpIndex = 0; grpIndex <= NUM_OF_GROUPS; grpIndex++) {
			for (int replIndex = 0; replIndex < numOfReplicas(); replIndex++) {
				JRef<Group> group = replicaSystem().lookup(
					name("group",grpIndex, replIndex), Group.class, JConsistencyLevels.STRONG);
				JRef<User> user = replicaSystem().lookup(
					name("user",grpIndex, replIndex), User.class, JConsistencyLevels.WEAK);

				groups.add(group);
				users.add(user);
			}
		}

		System.out.println("done");
	}

	@Override
	public void iteration() {
		for (int i = 0; i < NUM_OF_TRANSACTIONS; i++) {
			randomTransaction();
			System.out.print(i % 100 == 0 ? i : ".");
		}
		System.out.println();
	}

	@Override
	public void cleanup() {
		replicaSystem().clear(Sets.newHashSet());
	}



	private int transaction1() {
		int i = random.nextInt(groups.size());
		JRef<Group> group = groups.get(i);
		//   System.out.println(Thread.currentThread().getName() +  ": tx1 " + group);
		group.invoke("addPost", "Hello " + i);
		return 2;
	}

	private int transaction2() {
		int i = random.nextInt(users.size());
		JRef<User> user = users.get(i);
		// System.out.println(Thread.currentThread().getName() + ": tx2 " + user);

		//No sync
		Set<String> inbox = user.invoke("getInbox");
		return 1;
	}

	private int transaction2b() {
		int i = random.nextInt(users.size());
		JRef<User> user = users.get(i);
		// System.out.println(Thread.currentThread().getName() + ": tx2b " + user);

		JRef<Inbox> inbox = user.getField("inbox");
		user.sync();
		inbox.sync();
		Set<String> inboxVal = user.invoke("getInbox");

		return 0;
	}



	private int transaction3() {
		int i = random.nextInt(groups.size());
		int j = random.nextInt(users.size());

		JRef<Group> group = groups.get(i);
		JRef<User> user = users.get(j);

		//  System.out.println(Thread.currentThread().getName() + ": tx3 " + group + " " + user);
		group.invoke("addUser", user);

		return 3;
	}


	private int randomTransaction() {
		int rand = random.nextInt(100);
		if (rand < 58) /*12*/ {
			//inbox checking with sync
			return transaction2b();
		} else if (rand < 58) {
			return transaction2();
		} else if (rand < 80) {
			//Message posting
			return transaction1();
		} else if (rand < 100) {
			//group joining
			return transaction3();
		}
		//user creation: left out

		throw new IllegalStateException("cannot be here");
	}


}
