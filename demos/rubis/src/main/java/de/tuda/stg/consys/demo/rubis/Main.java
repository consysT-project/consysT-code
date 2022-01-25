package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

import scala.Option;
import scala.concurrent.duration.Duration;

import java.util.Scanner;
import java.util.UUID;

public class Main {
    private static final int msTimeout = 100;
    private static CassandraStoreBinding replica0;
    private static CassandraStoreBinding replica1;
    private static CassandraStoreBinding replica2;
    private static Server server0;
    private static Server server1;
    private static Server server2;
    private static Client client;

    public static void main(String[] args) {
        server0 = new Server(0, 3, null);
        server1 = new Server(1, 3, null);
        server2 = new Server(2, 3, null);

        client = new Client(null);

        Scanner commandLine = new Scanner(System.in);
        System.out.println("rubis client started\ntype 'connect' or 'init'");

        boolean running = true;
        String input = "";
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
                    case "store-0":
                        client.setStore(replica0);
                        break;
                    case "store-1":
                        client.setStore(replica1);
                        break;
                    case "store-2":
                        client.setStore(replica2);
                        break;
                    case "register": {
                        System.out.print("nickname: ");
                        var nickname = commandLine.nextLine();
                        System.out.print("real name: ");
                        var name = commandLine.nextLine();
                        System.out.print("password: ");
                        var password = commandLine.nextLine();
                        client.registerUser(name, nickname, password, "mail@example");
                        break;
                    }
                    case "login": {
                        System.out.print("nickname: ");
                        var nickname = commandLine.nextLine();
                        System.out.print("password: ");
                        var password = commandLine.nextLine();
                        client.loginUser(nickname, password);
                        break;
                    }
                    case "show-user":
                        System.out.println(client.printUserInfo());
                        break;
                    case "add-credits": {
                        System.out.print("amount: ");
                        var amount = commandLine.nextFloat();
                        commandLine.nextLine();
                        client.addBalance(amount);
                        break;
                    }
                    case "place-item": {
                        System.out.print("item name: ");
                        var name = commandLine.nextLine();
                        System.out.print("price: ");
                        var price = commandLine.nextFloat();
                        commandLine.nextLine();
                        System.out.print("duration: ");
                        var duration = commandLine.nextInt();
                        commandLine.nextLine();
                        client.registerItem(name, Category.MISC, price, duration);
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
                            return;
                        }
                        client.browseCategory(category);
                        break;
                    }
                    case "bid": {
                        System.out.print("item id: ");
                        var id = commandLine.nextLine();
                        System.out.print("bid value: ");
                        var price = commandLine.nextFloat();
                        commandLine.nextLine();
                        client.placeBid(UUID.fromString(id), price);
                        break;
                    }
                    case "buy": {
                        System.out.print("item id: ");
                        var id = commandLine.nextLine();
                        client.buyNow(UUID.fromString(id));
                        break;
                    }
                    case "exit":
                        running = false;
                        break;
                    default:
                        System.out.println("unknown command");
                        break;
                }
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        commandLine.close();
        System.out.println("rubis client stopped");

        try {
            if (replica0 != null)
                replica0.close();
            if (replica1 != null)
                replica1.close();
            if (replica2 != null)
                replica2.close();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }

    private static void initConnections(boolean clear) {
        replica0 = Cassandra.newReplica("127.0.0.1", 9042, 2181,
                Duration.apply(msTimeout, "ms"), clear);
        replica1 = Cassandra.newReplica("127.0.0.2", 9042, 2181,
                Duration.apply(msTimeout, "ms"), false);
        replica2 = Cassandra.newReplica("127.0.0.2", 9042, 2181,
                Duration.apply(msTimeout, "ms"), false);

        replica0.transaction(ctx -> {
            ctx.replicate("rubis", MIXED, Rubis.class);
            return Option.empty();
        });

        server0.setStore(replica0);
        server0.init();

        server1.setStore(replica1);
        server1.init();

        server2.setStore(replica2);
        server2.init();

        server0.start();
        server1.start();
        server2.start();

        client.setStore(replica0);
    }
}
