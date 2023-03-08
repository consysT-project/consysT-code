package de.tuda.stg.consys.triggerchat;


import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.concurrent.duration.Duration;

import java.util.Scanner;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

@SuppressWarnings({"consistency"})
public class InteractiveSession {
    private static final CassandraStoreBinding[] replicas = new CassandraStoreBinding[3];
    private static Session session;
    private static ExecutorService threadPool;

    public static void main(String[] args) {
        threadPool = Executors.newFixedThreadPool(1);

        Scanner commandLine = new Scanner(System.in);
        System.out.println("Client started. Type to send a message. ");

        boolean running = true;
        String input;
        initConnections();
        
        session.init();
        session.runSimulation();

        while(running){
            System.out.print("> ");
            input = commandLine.nextLine();
            try {
                session.sendMessage(input);
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
    }

    private static void closeConnections() {
        threadPool.shutdown();
        session.stopSimulation();
        try {
            for (var replica : replicas)
                replica.close();
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }
}
