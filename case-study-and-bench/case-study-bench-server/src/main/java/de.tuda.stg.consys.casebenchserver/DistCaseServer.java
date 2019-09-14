package de.tuda.stg.consys.casebenchserver;


import de.tuda.stg.consys.casebenchmarkdist.BenchmarkCommunication;
import de.tuda.stg.consys.casebenchmarkdist.ContentHandler;
import de.tuda.stg.consys.casestudy.Database;
import de.tuda.stg.consys.casestudy.ShoppingSite;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.Random;


/**
 * THIS IS THE SERVER FOR THE DISTRIBUTED BENCHMARK
 */
public class DistCaseServer {

    //Whether or not the benchmark replica system is connected
    static boolean benchmarkConnected;

    static Random r = new Random();

    static String[] loginUsers = new String[10];

    static JReplicaSystem thisSystem;

    static JRef<@Weak ShoppingSite> thisSite;

    static JRef<@Strong Database> database;

    static JRef<@Strong BenchmarkCommunication> comChannel;
    //This replicas turn to run the benchmark
    static int thisRunInfo;
    //This replicas turn to setup the benchmark
    static int thisSetupInfo;
    //The total amount of systems involved
    static int totalSystemCount;


    public static void main(String[] args) throws Exception {
        //Setup the replicas
        if(args.length == 0)
            readHostFile("");
        else
            readHostFile(args[0]);

        //Start the main loop function
        mainLoop();
    }

    //The main function which responds to the requirements of the benchmark
    public static void mainLoop() throws InterruptedException {



        while(!(boolean)comChannel.getField("finishedRunning")){
            //Keep running until benchmark finished running

            //Check if benchmmark is online
            if(!(boolean)comChannel.getField("benchmarkInstanceOnline")){
                benchmarkConnected = false;
            }

            //Check if benchmarking instance requested setup
            if(comChannel.getField("requestInstanceSetup")){
                setUpDatabase();
                fillDatabase();
                comChannel.setField("loginUsers", loginUsers);
                comChannel.setField("setupInstanceReady", true);
            }

            Thread.sleep(2000);
        }

    }

    public static void readHostFile(String hostfile) throws Exception{
        /*
        Layout for hosts.txt
        run;<This replicas turn to run>;<number of total replicas involved>
        (setup;<This replicas turn to setup the site to test>;<number of total replicas involved>)
        (load;<This replicas turn to create load>;<number of total replicas involved>)
        this;<This replicas ip/hostname>;<port of this replica>
        other;<other replica ip/hostname>;<port of other replica>
            ...
        other;<other replica ip/hostname>;<port of other replica>

        the setup line is optional if only 2 replica systems are involved, as it is obvious which replica does
        what when solely from the run order.
        the load line is optional, only needed if one host is supposed to create load.
        The order must be this order
        */
        LinkedList<String> fileCont = new LinkedList<>();

        if(hostfile.equals("")){
            try {
                BufferedReader bufferedReader =
                        new BufferedReader(new FileReader("hosts.txt"));

                String currLine;
                while((currLine = bufferedReader.readLine()) != null) {
                    fileCont.add(currLine);
                }
                bufferedReader.close();
            }
            catch(FileNotFoundException ex) {
                System.out.println(
                        "Host file needs to be in the same directory as the benchmark.");
                System.exit(0);
            }
        }
        else{
            try{
                BufferedReader bufferedReader = new BufferedReader(
                        new InputStreamReader(
                                new FileInputStream(hostfile), "UTF-8"));

                String currLine;
                while((currLine = bufferedReader.readLine()) != null) {
                    fileCont.add(currLine);
                }
                bufferedReader.close();
            }
            catch(FileNotFoundException ex) {
                System.out.println(
                        "Could not find host file at " + hostfile);
                System.exit(0);
            }
        }

        String[] runInfo = fileCont.remove().split(";");
        assert runInfo.length == 3;
        assert runInfo[0].equals("run");

        totalSystemCount = Integer.parseInt(runInfo[2]);
        thisRunInfo = Integer.parseInt(runInfo[1]);

        if(fileCont.getFirst().split(";")[0].equals("setup")){
            String[] setupInfo = fileCont.remove().split(";");
            assert setupInfo.length == 3;

            thisSetupInfo = Integer.parseInt(setupInfo[1]);
        }

        String[] otherHostInfo = new String[totalSystemCount-1];
        String load;
        String thisHost = "";

        try{
            for(int i= 0; i < totalSystemCount-1; i++) {
                String[] curr = fileCont.remove().split(";");
                if(curr[0].equals("load")) {
                    assert curr.length == 3;
                    load = curr[1] + ";" + curr[2];
                    curr = fileCont.remove().split(";");
                }
                if(curr[0].equals("this")) {
                    assert curr.length == 3;
                    thisHost = curr[1] + ";" + curr[2];
                    curr = fileCont.remove().split(";");
                }
                assert curr.length == 3;
                assert curr[0].equals("other");
                otherHostInfo[i] = curr[1] + ";" + curr[2];
            }
        }
        catch (Exception e) {
            System.out.println("Something went wrong while reading the host file, " +
                    "make sure it's correctly formatted.");
            System.exit(0);
        }

        //Make sure this host information was set correctly
        assert !thisHost.equals("");

        //Setup the replica systems
        String[] thisSplitHost = thisHost.split(";");
        thisSystem = JReplicaSystem.fromActorSystem(thisSplitHost[0], Integer.parseInt(thisSplitHost[1]));
        ///thisSystem = JReplicaSystem.fromActorSystem(thisPort);
        System.out.println("Created Replica System from '" + thisSplitHost[0] + "' on port '"
                + thisSplitHost[1] + "'");

        int addedcount = 0;

        while(addedcount < totalSystemCount -1){
            for (int i = 0; i < otherHostInfo.length; i++) {
                String otherHost = otherHostInfo[i];
                String[] hostSplit = otherHost.split(";");
                if(hostSplit.length < 3){
                    try{
                        int otherPort = Integer.parseInt(hostSplit [1]);
                        thisSystem.addReplicaSystem(hostSplit[0], otherPort);
                        System.out.println("Added Replica System from '" + hostSplit[0] + "' with port '"
                                + otherPort + "'");
                        otherHostInfo[i]= (otherHost + ";done");
                        addedcount++;
                    }
                    catch(Exception e){
                        System.out.println("Could not add Replica System");
                    }
                }
            }

            Thread.sleep(1000);
        }
        System.out.println("ADDED ALL REPLICAS: " + addedcount + "/" + (totalSystemCount-1));
        System.out.println("VERIFYING SUCCESSFUL INITIALIZATION");

        try{
            comChannel = thisSystem.replicate("comChannel", new BenchmarkCommunication(totalSystemCount), JConsistencyLevel.STRONG);
            System.out.println("Successfully established communication channel");
        }catch (Exception e){
            System.out.println("Communication Channel has already been established");
            comChannel = thisSystem.ref("comChannel", BenchmarkCommunication.class, JConsistencyLevel.STRONG);
        }

        while(!(boolean) comChannel.invoke("confirmReady")){
            System.out.println((String) comChannel.getField("msg"));
            comChannel.invoke("setReady", thisRunInfo);
            System.out.println("Not all systems ready yet, waiting for them to connect...");
            Thread.sleep(2000);
        }

        benchmarkConnected = true;
    }

    /*
    Function for setting up the database
    */
    private static boolean setUpDatabase(){
        database = thisSystem.replicate("database",
                new Database(), JConsistencyLevel.STRONG);
        return database.invoke("init");
    }

    private static boolean fillDatabase(){
        if(database != null){

            //Read products from pregenerated product file
            String[] products = ContentHandler.readFile("productsForBenchmark.txt");
            //If file is missing generate it
            if(products.length <= 0){
                products = ContentHandler.generateProducts(500);
                ContentHandler.writeFile("productsForBenchmark.txt", products);
            }

            //Add products to database
            database.invoke("AddInitialProducts", new ArrayList<>(Arrays.asList(products)));
            System.out.println("Added Products");

            //Read users from pregenerated product file
            String[] users = ContentHandler.readFile("usersForBenchmark.txt");
            //If file is missing generate it
            if(users.length <= 0){
                users = ContentHandler.generateUsers(500);
                ContentHandler.writeFile("usersForBenchmark.txt", users);
            }
            //Add random users to the login users
            for(int i = 0; i < loginUsers.length;i++){
                loginUsers[i] = users[r.nextInt(users.length)];
            }
            //Add users to database
            for (String user: users){
                String[] split = user.split(";");
                database.invoke("AddUser", split[0], split[1]);
            }
            System.out.println("Added Users");
            return true;
        }
        else
            return false;
    }
}
