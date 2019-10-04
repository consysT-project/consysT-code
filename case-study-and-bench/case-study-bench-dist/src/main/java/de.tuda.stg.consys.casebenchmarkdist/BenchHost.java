package de.tuda.stg.consys.casebenchmarkdist;


import com.sun.tools.javac.util.Pair;
import de.tuda.stg.consys.casestudy.Database;
import de.tuda.stg.consys.casestudy.Product;
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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.concurrent.TimeUnit;

/*
The benchmark for the endpoint of logging in
 */
public abstract class BenchHost {

    public static final int WARMUPCOUNT = 10;
    public static final int WARMUPREPETITIONS = 10;

    public static final int REPETITIONS = 1;

    public static int REQUEST_NUM;

    public static final NullOutputStream bh = new NullOutputStream();

    private static String requestsPath;

    private static String testVersion;

    private static String thisSystemInfo;

    private static String[] otherSystemInfo;

    private static JReplicaSystem thisSystem;

    private static JRef<? extends IDatabase> thisDatabase;

    private static JRef<? extends IShoppingSite> thisSite;

    private static JRef<@Strong ComChannel> comChannel;

    private static String outputName = "results.txt";

    /*
    Function for connecting the benchmark to the server
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

        if(getDatabaseRef() == null){
            System.out.println("Something went wrong with finding the database. Exiting!");
            System.exit(1);
        }


        //Adapt the requests to the necessary data structure and add them to the database
        prepareRequests();

        if(getShoppingsiteRef() == null){
            System.out.println("Something went wrong with creating the site. Exiting!");
            System.exit(1);
        }

        waitUntilReceived("setupDone");


        System.out.println("Setup Complete, Ready for benchmark.");
        return true;
    }

    //Method to be implemented that contains the code that will extract requests
    //and save them so they can be used by the benchmark
    static void prepareRequests() throws Exception {
        throw new Exception("Called Unimplemented Function of superclass");
    }

    private static boolean establishCommunication() throws InterruptedException {
        boolean foundComChannel = false;
        while(!foundComChannel){
            try{
                comChannel = thisSystem.ref("comChannel", ComChannel.class, JConsistencyLevel.STRONG);
                foundComChannel = true;
                System.out.println("Found Com Channel");
            }
            catch (Exception e){
                foundComChannel = false;
                System.out.println("Com Channel not yet found");
            }
        }

        while(!comChannel.isAvailable()){Thread.sleep(500);}

        comChannel.invoke("writeToServerQueue", "found");
        while((int) comChannel.invoke("benchQueueLength") <= 0){Thread.sleep(500);}
        if(((String)comChannel.invoke("popFromBenchQueue")).equals("confirmed")){
            System.out.println("Confirmed Com Channel");
            comChannel.invoke("writeToServerQueue", "confirmed");
            return true;
        }
        return false;
    }

    private static JRef<? extends IDatabase> getDatabaseRef() throws InterruptedException {
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
        while(!thisDatabase.isAvailable()){Thread.sleep(500);}
        return thisDatabase;
    }

    private static JRef<? extends IShoppingSite> getShoppingsiteRef() throws InterruptedException {
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
        while(!thisSite.isAvailable()){Thread.sleep(500);}
        return thisSite;
    }

    private static String[] getRequests(){
        return ContentHandler.readFile(requestsPath);
    }

    /*
    Methods to warm up during benchmarking,
    this should include the benchmarking method, but also teardown methods needed between invocations.
     */
    private static void warmUpBench() throws Exception {
        System.out.println("Started Warm Up");
        for(int  i = 0; i < WARMUPCOUNT; i++){
            for (int  j = 0; j < WARMUPREPETITIONS; j++){
                boolean valid = true;
                boolean retVal = false;
                requestPrep();
                try{
                    retVal = request(0);
                }catch(Exception e){
                    valid = false;
                }
                if(valid)
                    requestTeardown();
                bh.write(((retVal) ? 1 : 0));
            }
            System.out.print("\rWarming Up: "+(i+1)+"/"+WARMUPCOUNT);
        }
        System.out.println("Finished Warm Up");
    }

    private static void runBenchmark() throws Exception {
        System.out.println("Started Benchmark");
        PrintWriter writer = new PrintWriter(outputName, "UTF-8");
        for (int i = 0;i < REQUEST_NUM;i++) {
            boolean valid = true;
            boolean retVal = false;
            requestPrep();
            long firstTime = System.nanoTime();
            try{
                retVal = request(i);
            }catch(Exception e){
                System.out.println("Failed");
                valid = false;
            }
            //Add code here to write result into blackhole, if nescessary
            long sndTime = System.nanoTime();
            if(valid){
                long time = TimeUnit.NANOSECONDS.toMillis(sndTime - firstTime);
                System.out.print("\rSuccess: " + time + " | ");
                writer.println(time);
                requestTeardown();
            } else i--;

            //updateProgress(((retVal) ? "1" : "0"));
            bh.write(((retVal) ? 1 : 0));
            updateProgress(i+1);
        }
        writer.close();
        System.out.println("Finished Benchmark");
    }

    private static void updateProgress(int prog) throws Exception {
        throw new Exception("Called Unimplemented UpdateProgress of superclass");
    }

    /*
    Method executed before every request
    */
    private static void requestPrep() throws Exception {
        throw new Exception("Called Unimplemented RequestPrep Function of superclass");
    }

    /*
    The method that will be measured during benchmarking
     */
    private static boolean request(int requestnumber) throws Exception {
        throw new Exception("Called Unimplemented Request Function of superclass");
    }

    /*
    Method executed after every request
     */
    private static void requestTeardown() throws Exception {
        throw new Exception("Called Unimplemented RequestTeardown Function of superclass");
    }

    private static void exitBench() throws Exception {
        comChannel.invoke("writeToServerQueue", "abort");
        thisSystem.close();
    }

    private static void waitUntilReceived(String msg) throws InterruptedException {
        while(true){
            String ret = comChannel.invoke("popFromBenchQueue");
            if(ret != null)
                if(ret.equals(msg))
                    return;
            Thread.sleep(500);
        }
    }
}
