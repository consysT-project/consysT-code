package de.tuda.stg.consys.demo.messagegroups;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.messagegroups.schema.Group;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.objects.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Set;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class ContentionMessageGroupsBenchmark extends DemoBenchmark {


	public static void main(String[] args) {
		start(ContentionMessageGroupsBenchmark.class, args[0]);
	}

	private final int numOfGroupsPerReplica;
	private final int numOfTransactions;

	private final List<JRef<Group>> groups;
	private final List<JRef<User>> users;

	private final Random random = new Random();

	public ContentionMessageGroupsBenchmark(Config config) {
		super(config);

		numOfGroupsPerReplica = config.getInt("consys.bench.demo.messagegroups.groups");
		numOfTransactions = config.getInt("consys.bench.demo.messagegroups.transactions");

		groups = new ArrayList<>(numOfGroupsPerReplica * numOfReplicas());
		users = new ArrayList<>(numOfGroupsPerReplica * numOfReplicas());

		setStepsPerIteration(numOfTransactions);
		setWaitPerIteration(1);
	}

	private static String addr(String identifier, int grpIndex, int replIndex) {
		return identifier + "$" + grpIndex + "$"+ replIndex;
	}


	private int numOfReplicas() {
		return replicaSystem().numOfReplicas();
	}

	@Override
	public void setup() {
		System.out.println("Adding users");
		for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {

			JRef<Group> group = replicaSystem().replicate(
				addr("group", grpIndex, processId()), new Group(), getStrongLevel());
			JRef<Inbox> inbox =  replicaSystem().replicate(
				addr("inbox", grpIndex, processId()), new Inbox(), getWeakLevel());
			JRef<User> user = replicaSystem().replicate(
				addr("user", grpIndex, processId()), new User(inbox, addr("alice", grpIndex, processId())), getWeakLevel());

			DemoUtils.printProgress(grpIndex);
		}
		DemoUtils.printDone();

		replicaSystem().barrier("users_added");

		for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
			for (int replIndex = 0; replIndex < numOfReplicas(); replIndex++) {
				JRef<Group> group = replicaSystem().lookup(
					addr("group",grpIndex, replIndex), Group.class, getStrongLevel());
				JRef<User> user = replicaSystem().lookup(
					addr("user",grpIndex, replIndex), User.class, getWeakLevel());


				if (replIndex == processId()) group.ref().addUser(user);

				groups.add(group);
				users.add(user);
			}
			DemoUtils.printProgress(grpIndex);
		}
		DemoUtils.printDone();
	}



	@Override
	public void iteration() {
		randomTransaction();
		System.out.print(".");
	}

	@Override
	public void cleanup() {
		replicaSystem().clear(Sets.newHashSet());
	}



	private int transaction1() {
		int i = random.nextInt(groups.size());
		JRef<Group> group = groups.get(i);
		//   System.out.println(Thread.currentThread().getName() +  ": tx1 " + group);
		group.ref().addPost("Hello " + i);
		return 2;
	}

	private int transaction2() {
		int i = random.nextInt(users.size());
		JRef<User> user = users.get(i);
		// System.out.println(Thread.currentThread().getName() + ": tx2 " + user);

		//No sync
		Set<String> inbox = user.ref().getInbox();
		return 1;
	}

	private int transaction2b() {
		int i = random.nextInt(users.size());
		JRef<User> user = users.get(i);
		// System.out.println(Thread.currentThread().getName() + ": tx2b " + user);

		JRef<Inbox> inbox = user.ref().inbox;
		if (random.nextInt(100) < 20) {
			user.sync();
			inbox.sync();
		}
		Set<String> inboxVal = user.ref().getInbox();

		return 0;
	}



	private int transaction3() {
		int i = random.nextInt(groups.size());
		int j = random.nextInt(users.size());

		JRef<Group> group = groups.get(i);
		JRef<User> user = users.get(j);

		//  System.out.println(Thread.currentThread().getName() + ": tx3 " + group + " " + user);
		group.ref().addUser(user);

		return 3;
	}


	private int randomTransaction() {
		int rand = random.nextInt(100);
		if (rand < 58) /*12*/ {
			//inbox checking with sync
			return transaction2(); //use 2b for syncing here
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
