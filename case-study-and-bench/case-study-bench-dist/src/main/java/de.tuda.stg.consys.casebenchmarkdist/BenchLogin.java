package de.tuda.stg.consys.casebenchmarkdist;


import com.sun.tools.javac.util.Pair;
import de.tuda.stg.consys.casestudy.Database;
import de.tuda.stg.consys.casestudyinterface.IDatabase;
import de.tuda.stg.consys.casestudyinterface.IShoppingSite;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import org.openjdk.jmh.util.NullOutputStream;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.concurrent.TimeUnit;

/*
The benchmark for the endpoint of logging in
 */
public class BenchLogin {

    public static final int WARMUPCOUNT = 100000;
    public static final int WARMUPREPETITIONS = 100;

    public static final int REPETITIONS = 1;

    public static final NullOutputStream bh = new NullOutputStream();

    static Pair<String,String>[] logins;

    private static String requestsPath;

    private static String testVersion;

    private static String thisSystemInfo;

    private static String[] otherSystemInfo;

    private static JReplicaSystem thisSystem;

    private static JRef<? extends IDatabase> thisDatabase;

    private static JRef<? extends IShoppingSite> thisSite;

    private static JRef<@Strong ComChannel> comChannel;

    public static void main (String[] args) throws InterruptedException {
        if(args.length < 4){
            System.out.println("Wrong parameter count");
            System.exit(1);
        }
        requestsPath = args[0];
        testVersion = args[1];
        thisSystemInfo = args[2];
        otherSystemInfo = Arrays.copyOfRange(args, 3,args.length);

        connect();
    }

    /*
    Function for connecting the benchmark to the server
     */
    public static boolean connect() throws InterruptedException {
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

        if(getDatabaseRef() == null){
            System.out.println("Something went wrong with finding the database. Exiting!");
            System.exit(1);
        }

        comChannel = thisSystem.ref("comChannel", ComChannel.class, JConsistencyLevel.STRONG);

        String[] allLogins = getRequests();
        ArrayList<Pair<String,String>> templist = new ArrayList<>();

        //Adapt the requests to the necessary data structure and add them to the database
        for (String thisLogin: allLogins) {
            String[] split = thisLogin.split(";");
            templist.add(new Pair<>(split[0],split[1]));
            thisDatabase.invoke("AddUser", split[0], split[1]);
        }
        logins = (Pair<String,String>[]) templist.toArray();

        if(getShoppingsiteRef() == null){
            System.out.println("Something went wrong with creating the site. Exiting!");
            System.exit(1);
        }

        String[] requests = getRequests();

        System.out.println("Setup Complete, Ready for benchmark.");
        return true;
    }

    private static JRef<? extends IDatabase> getDatabaseRef(){
        boolean foundDatabase = false;
        while(!foundDatabase){
            switch (testVersion){
                case "mixed":
                    try{
                        thisDatabase = thisSystem.ref("database", de.tuda.stg.consys.casestudy.Database.class, JConsistencyLevel.STRONG);
                        foundDatabase = true;
                    }
                    catch (Exception e){ }
                    break;
                case "strong":
                    try{
                        thisDatabase = thisSystem.ref("database", de.tuda.stg.consys.casestudystrong.Database.class, JConsistencyLevel.STRONG);
                        foundDatabase = true;
                    }
                    catch (Exception e){ }
                    break;
                default:
                    thisDatabase = null;
                    break;
            }
        }
        return thisDatabase;
    }

    private static JRef<? extends IShoppingSite> getShoppingsiteRef(){
        switch (testVersion){
            case "mixed":
                thisSite = thisSystem.replicate(new de.tuda.stg.consys.casestudy.ShoppingSite(
                        (JRef<de.tuda.stg.consys.casestudy.Database>) thisDatabase), JConsistencyLevel.STRONG);
                break;
            case "strong":
                thisSite = thisSystem.replicate( new de.tuda.stg.consys.casestudystrong.ShoppingSite(
                        (JRef<de.tuda.stg.consys.casestudystrong.Database>) thisDatabase), JConsistencyLevel.STRONG);
                break;
            default:
                thisSite = null;
                break;
        }

        return thisSite;
    }

    private static String[] getRequests(){
        return ContentHandler.readFile(requestsPath);
    }

    private static void runBenchmark() throws IOException {
        warmUpBench();
        PrintWriter writer = new PrintWriter("result.txt", "UTF-8");
        for (int i = 0;i < logins.length;i++) {
            requestPrep();

            long firstTime = System.nanoTime();
            boolean retVal = request(i);
            //Add code here to write result into blackhole, if nescessary
            long sndTime = System.nanoTime();
            writer.println(TimeUnit.NANOSECONDS.toMillis(sndTime - firstTime));
            requestTeardown();
            bh.write(((retVal) ? 1 : 0));
        }
        writer.close();
    }

    /*
    Methods to warm up during benchmarking,
    this should include the benchmarking method, but also teardown methods needed between invocations.
     */
    private static void warmUpBench() throws IOException {
        for(int  i = 0; i < WARMUPCOUNT; i++){
            for (int  j = 0; j < WARMUPREPETITIONS; j++){
                requestPrep();
                boolean retVal = request(0);
                requestTeardown();
                bh.write(((retVal) ? 1 : 0));
            }
        }
    }

    /*
    Method executed before every request
    */
    private static void requestPrep(){
        //In the case of login, no prep is needed
    }

    /*
    The method that will be measured during benchmarking
     */
    private static boolean request(int requestnumber){
        //Log in
        return thisSite.invoke("Login", logins[requestnumber].fst,
                logins[requestnumber].snd);
    }

    /*
    Method executed after every request
     */
    private static void requestTeardown(){
        //Log out after each login
        thisSite.invoke("Logout");
    }
}
