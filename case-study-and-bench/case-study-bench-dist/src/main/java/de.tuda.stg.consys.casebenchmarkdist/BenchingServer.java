package de.tuda.stg.consys.casebenchmarkdist;

import de.tuda.stg.consys.casestudy.Product;
import de.tuda.stg.consys.casestudy.User;
import de.tuda.stg.consys.casestudyinterface.IDatabase;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

/**
 * The "Server" part of the benchmarks which is responsible for setting up the database and such and to reset things if
 * required by the benchmark.
 */
public class BenchingServer {

    private static String usersPath;

    private static String productsPath;

    private static String testVersion;

    private static String thisSystemInfo;

    private static String[] otherSystemInfo;

    private static JReplicaSystem thisSystem;

    private static JRef<? extends IDatabase> thisDatabase;

    private static JRef<@Strong ComChannel> comChannel;

    public static void main (String[] args) throws Exception {
        if(args.length < 5){
            System.out.println("Wrong parameter count");
            System.exit(1);
        }
        usersPath = args[0];
        productsPath = args[1];
        testVersion = args[2];
        thisSystemInfo = args[3];
        otherSystemInfo = Arrays.copyOfRange(args, 4,args.length);

        connect();
        System.out.println("Finished Connection");
        mainLoop();
        exitBench();
        System.exit(1);
    }

    public static void mainLoop() throws InterruptedException {
        System.out.println("Entered Main Loop");
        while(true){
            if((int) comChannel.invoke("serverQueueLength") > 0){
                switch ((String) comChannel.invoke("popFromServerQueue")){
                    case "abort":
                        return;
                    default:
                        System.out.println("Did not recognize message");
                        break;
                }
            }
            Thread.sleep(500);
        }
    }

    /*
    Function for connecting the server to the benchmark
     */
    public static boolean connect() throws Exception {
        String[] thisSystemInfoSplit = thisSystemInfo.split(";");
        thisSystem = JReplicaSystem.fromActorSystem(thisSystemInfoSplit[0],Integer.parseInt(thisSystemInfoSplit[1]));

        int addedcount = 0;

        while(addedcount < otherSystemInfo.length){
            for (int i = 0; i < otherSystemInfo.length; i++) {
                String otherHost = otherSystemInfo[i];
                String[] hostSplit = otherHost.split(";");
                if(hostSplit.length < 3){
                    try{
                        int otherPort = Integer.parseInt(hostSplit [1]);
                        thisSystem.addReplicaSystem(hostSplit[0], otherPort);
                        System.out.println("Added Replica System from '" + hostSplit[0] + "' with port '"
                                + otherPort + "'");
                        otherSystemInfo[i]= (otherHost + ";done");
                        addedcount++;
                    }
                    catch(Exception e){
                        System.out.println("Could not add Replica System");
                    }
                }
            }

            Thread.sleep(1000);
        }
        System.out.println("ADDED ALL REPLICAS: " + addedcount + "/" + (otherSystemInfo.length));

        establishCommunication();

        System.out.println("Established Communication");

        String[] allUsers = getUsers();
        String[] allProds = getProducts();

        if(getDatabaseRef((int)((double) allUsers.length / 0.7),(int)((double) allProds.length / 0.7)) == null){
            System.out.println("Something went wrong with database creation. Exiting!");
            System.exit(1);
        }

        System.out.println("Created Database");

        thisDatabase.invoke("AddInitialProducts", new ArrayList<>(Arrays.asList(allProds)));
        System.out.println("Added Products");

        for (int i = 0; i < allUsers.length; i++){
            String[] thisUserSplit = allUsers[i].split(";");
            thisDatabase.invoke("AddUser", thisUserSplit[0], thisUserSplit[1]);
            System.out.print("\radded " + (i+1) + "/" + allUsers.length + " Users");
        }
        System.out.println("");
        System.out.println("Setup Complete, Ready for benchmark.");
        comChannel.invoke("writeToBenchQueue","setupDone");
        System.out.println("Wrote setup confirmation to bench");
        return true;
    }

    private static boolean establishCommunication() throws InterruptedException {
        boolean createdComChannel = false;
        while(!createdComChannel){
            try{
                comChannel = thisSystem.replicate("comChannel", new ComChannel(), JConsistencyLevel.STRONG);
                System.out.println("Created Com Channel");
                createdComChannel = true;
            }
            catch (Exception e){
                createdComChannel = false;
            }
        }
        comChannel.sync();
        while((int) comChannel.invoke("serverQueueLength") <= 0){Thread.sleep(500);}
        if(((String)comChannel.invoke("popFromServerQueue")).equals("found")){
            System.out.println("Bench found Channel");
            comChannel.invoke("writeToBenchQueue", "confirmed");
        }
        while((int) comChannel.invoke("serverQueueLength") <= 0){Thread.sleep(500);}
        if(((String)comChannel.invoke("popFromServerQueue")).equals("confirmed")){
            System.out.println("Confirmed Com Channel");
            return true;
        }
        return false;
    }

    private static JRef<? extends IDatabase> getDatabaseRef(int initUserCount, int initProductCount){
        switch (testVersion){
            case "mixed":
                thisDatabase = thisSystem.replicate("database", new de.tuda.stg.consys.casestudy.Database(), JConsistencyLevel.STRONG);
                while(!thisDatabase.isAvailable()){ }
                thisDatabase.invoke("init",initUserCount, initProductCount);
                break;
            case "strong":
                thisDatabase = thisSystem.replicate("database", new de.tuda.stg.consys.casestudystrong.Database(), JConsistencyLevel.STRONG);
                while(!thisDatabase.isAvailable()){ }
                thisDatabase.invoke("init",initUserCount, initProductCount);
                break;
            default:
                thisDatabase = null;
                break;
        }

        return thisDatabase;
    }

    private static String[] getUsers(){
        return ContentHandler.readFile(usersPath);
    }

    private static String[] getProducts(){
        return ContentHandler.readFile(productsPath);
    }

    private static void exitBench() throws Exception {
        thisSystem.close();
    }
}
