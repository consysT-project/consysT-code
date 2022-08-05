package de.tuda.stg.consys.demo.rubis.extras;

import de.tuda.stg.consys.demo.rubis.AppException;
import de.tuda.stg.consys.demo.rubis.Session;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

import scala.Option;
import scala.concurrent.duration.Duration;

import java.util.Scanner;
import java.util.UUID;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

@SuppressWarnings({"consistency"})
public class InteractiveSession {
    private static final int msTimeout = 100;
    private static final int msServerSleep = 1000;
    private static final CassandraStoreBinding[] replicas = new CassandraStoreBinding[3];
    private static final BackgroundTask[] backgroundTasks = new BackgroundTask[3];
    private static Session session;
    private static ExecutorService threadPool;

    public static void main(String[] args) {
        threadPool = Executors.newFixedThreadPool(backgroundTasks.length);

        Scanner commandLine = new Scanner(System.in);
        System.out.println("auction client started\ntype 'connect' or 'init'");

        boolean running = true;
        String input;
        while(running){
            System.out.print("> ");
            input = commandLine.nextLine();
            try {
                switch(input) {
                    case "init":
                        initConnections(true);
                        break;
                    case "connect":
                        initConnections(false);
                        break;
                    case "set store": {
                        System.out.print("id: ");
                        var id = commandLine.nextInt();
                        commandLine.nextLine();
                        switch (id) {
                            case 0: session.setStore(replicas[0]); break;
                            case 1: session.setStore(replicas[1]); break;
                            case 2: session.setStore(replicas[2]); break;
                            default: System.out.println("unknown store");
                        }
                        break;
                    }
                    case "register": {
                        System.out.print("nickname: ");
                        var nickname = commandLine.nextLine();
                        System.out.print("real name: ");
                        var name = commandLine.nextLine();
                        System.out.print("password: ");
                        var password = commandLine.nextLine();
                        session.registerUser(null, nickname, name, password, "mail@example");
                        break;
                    }
                    case "login": {
                        System.out.print("nickname: ");
                        var nickname = commandLine.nextLine();
                        System.out.print("password: ");
                        var password = commandLine.nextLine();
                        session.loginUser(null, nickname, password);
                        break;
                    }
                    case "show user":
                        System.out.println(session.printUserInfo(null, false));
                        break;
                    case "show full user":
                        System.out.println(session.printUserInfo(null, true));
                        break;
                    case "add credits": {
                        System.out.print("amount: ");
                        var amount = commandLine.nextFloat();
                        commandLine.nextLine();
                        session.addBalance(null, amount);
                        break;
                    }
                    case "place item": {
                        System.out.print("item name: ");
                        var name = commandLine.nextLine();
                        System.out.print("price: ");
                        var price = commandLine.nextFloat();
                        commandLine.nextLine();
                        System.out.print("duration: ");
                        var duration = commandLine.nextInt();
                        commandLine.nextLine();
                        UUID item = session.registerItem(null, name, "", Category.MISC, price, duration);
                        System.out.println("New item: " + item);
                        break;
                    }
                    case "browse": {
                        System.out.print("category: ");
                        var categoryName = commandLine.nextLine();
                        Category category;
                        try {
                            category = Category.valueOf(categoryName);
                        } catch (IllegalArgumentException e) {
                            System.out.println("unknown category");
                            break;
                        }
                        System.out.println(session.browseCategory(null, category, 10));
                        break;
                    }
                    case "bid": {
                        System.out.print("item id: ");
                        var id = commandLine.nextLine();
                        System.out.print("bid value: ");
                        var price = commandLine.nextFloat();
                        commandLine.nextLine();
                        session.placeBid(null, UUID.fromString(id), price);
                        break;
                    }
                    case "buy": {
                        System.out.print("item id: ");
                        var id = commandLine.nextLine();
                        session.buyNow(null, UUID.fromString(id));
                        break;
                    }
                    case "end auction": {
                        System.out.print("item id: ");
                        var id = commandLine.nextLine();
                        session.endAuctionImmediately(null, UUID.fromString(id));
                        break;
                    }
                    case "exit":
                        running = false;
                        break;
                    default:
                        System.out.println("unknown command");
                        break;
                }
            } catch (AppException e) {
                System.out.println(e.getMessage());
            } catch (Exception e) {
                System.out.println(e.getMessage());
                e.printStackTrace();
            }
        }
        commandLine.close();
        System.out.println("auction client stopped");
        closeConnections();
        System.out.println("auction servers stopped");
    }

    private static void initConnections(boolean clear) {
        for (int i = 0; i < replicas.length; i++)
            replicas[i] = CassandraReplica.create("127.0.0." + (i+1), 9042, 2181,
                Duration.apply(msTimeout, "ms"), i == 0 && clear);

        if (clear) {
            replicas[0].transaction(ctx -> {
                ctx.replicate(Util.auctionStoreKey, MIXED, AuctionStore.class);
                return Option.empty();
            });
        }

        for (int i = 0; i < backgroundTasks.length; i++) {
            backgroundTasks[i] = new BackgroundTask(i, replicas.length, msServerSleep, replicas[i % replicas.length]);
            backgroundTasks[i].init();
            threadPool.submit(backgroundTasks[i]);
        }

        session = new Session(replicas[0]);
    }

    private static void closeConnections() {
        for (var task : backgroundTasks)
            task.stopThread();

        threadPool.shutdown();
        //threadPool.awaitTermination(5, TimeUnit.SECONDS);

        try {
            for (var replica : replicas)
                replica.close();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }
}
