package de.tuda.stg.consys.demo.webshop.extras;


import de.tuda.stg.consys.demo.webshop.Session;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.concurrent.duration.Duration;
import java.util.Scanner;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

@SuppressWarnings({"consistency"})
public class InteractiveSession {
    private static final CassandraStoreBinding[] replicas = new CassandraStoreBinding[1];
    private static Session session;
    private static BackgroundTask backgroundTask;
    private static ExecutorService threadPool;

    public static void main(String[] args) {
        threadPool = Executors.newFixedThreadPool(1);

        Scanner commandLine = new Scanner(System.in);
        System.out.println("Client started.");
        System.out.println("'list': List all products");
        System.out.println("'balance': Check your balance");
        System.out.println("'buy': Buy a product");
        System.out.println("'exit': Quit");

        boolean running = true;
        String input;
        initConnections();
        
        session.initProducts();
        session.initUser();
        //session.runBalanceChecker();

        //threadPool.submit(backgroundTask);

        while(running){
            System.out.print("> ");
            input = commandLine.nextLine();
            try {
                switch(input) {
                    case "list": {
                        session.showProducts();
                        break;
                    }
                    case "buy": {
                        var name = "";

                        while(true) {
                            System.out.print("Product name: ");
                            name = commandLine.nextLine();

                            if (!name.isEmpty()) {
                                break;
                            }
                        }

                        System.out.print("Amount: ");
                        var amount = commandLine.nextLine();
                        session.buyProduct(name, Integer.parseInt(amount));
                        break;
                    }
                    case "balance": {
                        session.showBalance();
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
                System.out.println(e.getMessage());
                e.printStackTrace();
            }
        }
        commandLine.close();
        System.out.println("Client stopped");
        closeConnections();
        System.out.println("Servers stopped");
    }

    private static void initConnections() {
        int zookeeperPort = 2181;
        for (int i = 0; i < replicas.length; i++)
            replicas[i] = CassandraReplica.create("127.0.0." + (i+1), 9042, zookeeperPort + i, Duration.apply(15, "s"), i == 0);

        session = new Session(replicas[0]);
        //backgroundTask = new BackgroundTask(replicas[1]);
    }

    private static void closeConnections() {
        session.stopBalanceChecker();
        backgroundTask.stopThread();
        threadPool.shutdown();

        try {
            for (var replica : replicas)
                replica.close();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }
}
