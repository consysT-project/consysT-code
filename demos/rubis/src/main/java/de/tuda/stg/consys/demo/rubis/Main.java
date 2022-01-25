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

    public static void main(String[] args) {
        CassandraStoreBinding replica0 = null;
        CassandraStoreBinding replica1 = null;
        CassandraStoreBinding replica2 = null;

        Server server0 = new Server(0, 3, null);
        Server server1 = new Server(1, 3, null);
        Server server2 = new Server(2, 3, null);

        Client client = new Client(null);

        Scanner commandLine = new Scanner(System.in);
        System.out.println("rubis client started\ntype 'connect' or 'init'");

        boolean running = true;
        String input = "";
        while(running){
            System.out.print("> ");
            input = commandLine.nextLine();
            switch(input) {
                case "init":
                    replica0 = Cassandra.newReplica("127.0.0.1", 9042, 2181,
                            Duration.apply(msTimeout, "ms"), true);
                    replica1 = Cassandra.newReplica("127.0.0.2", 9042, 2181,
                            Duration.apply(msTimeout, "ms"), false);
                    replica2 = Cassandra.newReplica("127.0.0.2", 9042, 2181,
                            Duration.apply(msTimeout, "ms"), false);
                    replica0.transaction(ctx -> {
                        ctx.replicate("rubis", WEAK, Rubis.class);
                        return Option.empty();
                    });
                    client.setStore(replica0);
                    server0.setStore(replica0);
                    server0.init();
                    server0.start();
                    server1.setStore(replica1);
                    server1.init();
                    server1.start();
                    server2.setStore(replica2);
                    server2.init();
                    server2.start();
                    break;
                case "connect":
                    replica0 = Cassandra.newReplica("127.0.0.1", 9042, 2181,
                            Duration.apply(msTimeout, "ms"), false);
                    replica1 = Cassandra.newReplica("127.0.0.2", 9042, 2181,
                            Duration.apply(msTimeout, "ms"), false);
                    replica2 = Cassandra.newReplica("127.0.0.2", 9042, 2181,
                            Duration.apply(msTimeout, "ms"), false);
                    client.setStore(replica0);
                    server0.setStore(replica0);
                    server0.init();
                    server0.start();
                    server1.setStore(replica1);
                    server1.init();
                    server1.start();
                    server2.setStore(replica2);
                    server2.init();
                    server2.start();
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
                case "register-user": {
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
                case "register-item": {
                    System.out.print("item name: ");
                    var name = commandLine.nextLine();
                    System.out.print("price: ");
                    var price = commandLine.nextFloat();
                    commandLine.nextLine();
                    client.registerItem(name, price);
                    break;
                }
                case "browse":
                    System.out.print("category: ");
                    var categoryName = commandLine.nextLine();
                    client.browseCategory(categoryName);
                    break;
                case "bid": {
                    System.out.print("item name: ");
                    var name = commandLine.nextLine();
                    System.out.print("bid value: ");
                    var price = commandLine.nextFloat();
                    commandLine.nextLine();
                    client.placeBid(name, price);
                    break;
                }
                case "exit":
                    running = false;
                    break;
                default:
                    System.out.println("unknown command");
                    break;
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
}
