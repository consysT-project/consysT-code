package de.tuda.stg.consys.casebenchmarkdist;

import de.tuda.stg.consys.casestudyinterface.IDatabase;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * The "Server" part of the benchmarks which is responsible for setting up the database and such and to reset things if
 * required by the benchmark.
 */
public class BenchingServer {

    private static String loginsPath;

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
        loginsPath = args[0];
        productsPath = args[1];
        testVersion = args[2];
        thisSystemInfo = args[3];
        otherSystemInfo = Arrays.copyOfRange(args, 4,args.length);

        connect();
        mainLoop();
    }

    public static void mainLoop() throws InterruptedException {
        while(true){
            if((int) comChannel.invoke("queueLength") > 0){
                switch ((String) comChannel.invoke("popFromQueue")){
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

        exitBench();
        System.exit(1);

        if(getDatabaseRef() == null){
            System.out.println("Something went wrong with database creation. Exiting!");
            System.exit(1);
        }

        thisDatabase.invoke("AddInitialProducts", new ArrayList<>(Arrays.asList(getProducts())));

        String[] allLogins = getLogins();
        for (String thisLogin: allLogins) {
            String[] thisLoginSplit = thisLogin.split(";");
            thisDatabase.invoke("AddUser", thisLoginSplit[0], thisLoginSplit[1]);
        }
        System.out.println("Setup Complete, Ready for benchmark.");
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

    private static JRef<? extends IDatabase> getDatabaseRef(){
        switch (testVersion){
            case "mixed":
                thisDatabase = thisSystem.replicate("database", new de.tuda.stg.consys.casestudy.Database(), JConsistencyLevel.STRONG);
                thisDatabase.invoke("init");
                break;
            case "strong":
                thisDatabase = thisSystem.replicate("database", new de.tuda.stg.consys.casestudystrong.Database(), JConsistencyLevel.STRONG);
                thisDatabase.invoke("init");
                break;
            default:
                thisDatabase = null;
                break;
        }

        return thisDatabase;
    }

    private static String[] getLogins(){
        return ContentHandler.readFile(loginsPath);
    }

    private static String[] getProducts(){
        return ContentHandler.readFile(productsPath);
    }

    private static void exitBench() throws Exception {
        thisSystem.close();
    }
}
