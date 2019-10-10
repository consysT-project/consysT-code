package de.tuda.stg.consys.casebenchmarkdist;

import de.tuda.stg.consys.casestudyinterface.IDatabase;
import de.tuda.stg.consys.casestudyinterface.IShoppingSite;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import org.openjdk.jmh.util.NullOutputStream;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.concurrent.TimeUnit;

public class BenchCheckout{

    public static final int WARMUPCOUNT = 10;
    public static final int WARMUPREPETITIONS = 1;

    public static final int REPETITIONS = 1;

    public static final NullOutputStream bh = new NullOutputStream();

    static String[][] checkoutReqs;

    private static String requestsPath;

    private static String testVersion;

    private static String thisSystemInfo;

    private static String[] otherSystemInfo;

    private static JReplicaSystem thisSystem;

    private static JRef<? extends IDatabase> thisDatabase;

    private static JRef<? extends IShoppingSite> thisSite;

    private static JRef<@Strong ComChannel> comChannel;

    private static String outputName = "results.txt";

    public static void main (String[] args) throws Exception {
        if(args.length < 4){
            System.out.println("Wrong parameter count");
            System.exit(1);
        }
        requestsPath = args[0];
        testVersion = args[1];
        int off = 0;
        if (args[2].equals("-o")) {
            outputName = args[3];
            off = 2;
        }
        thisSystemInfo = args[2+off];
        otherSystemInfo = Arrays.copyOfRange(args, 3+off,args.length);

        connect();
        warmUpBench();
        runBenchmark();
        exitBench();
        System.exit(1);
    }

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
        String[] allReqs = getRequests();
        checkoutReqs = new String[allReqs.length][5];
        for (int i = 0;i<allReqs.length;i++) {
            checkoutReqs[i] = allReqs[i].split(";");
        }
        // Add cart reqs: username;password;searchword;sizeofreturned;numberofelements

        if(getShoppingsiteRef() == null){
            System.out.println("Something went wrong with creating the site. Exiting!");
            System.exit(1);
        }

        waitUntilReceived("setupDone");


        System.out.println("Setup Complete, Ready for benchmark.");
        return true;
    }

    private static boolean establishCommunication() throws InterruptedException {
        boolean foundComChannel = false;
        while(!foundComChannel){
            try{
                comChannel = thisSystem.lookup("comChannel", ComChannel.class, JConsistencyLevel.STRONG);
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
                        thisDatabase = thisSystem.lookup("database", de.tuda.stg.consys.casestudy.Database.class, JConsistencyLevel.STRONG);
                        foundDatabase = true;
                    }
                    catch (Exception e){ }
                    break;
                case "strong":
                    try{
                        thisDatabase = thisSystem.lookup("database", de.tuda.stg.consys.casestudystrong.Database.class, JConsistencyLevel.STRONG);
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

    private static void runBenchmark() throws IOException {
        System.out.println("Started Benchmark");
        PrintWriter writer = new PrintWriter(outputName, "UTF-8");
        long allTimes = 0;
        for (int i = 0; i < checkoutReqs.length; i++) {
            long firstOut = System.nanoTime();

            boolean valid = true;
            boolean retVal = false;
            requestPrep(i);
            long firstTime = System.nanoTime();
            try{
                retVal = request(i);
            }catch(Exception e){
                System.out.print("Failed");
                throw e;
                //valid = false;
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
            eatObject(retVal);
            System.out.print(Integer.toString(i+1) + " / " + checkoutReqs.length);

            allTimes = (allTimes+ (System.nanoTime() - firstOut));
            long time = TimeUnit.NANOSECONDS.toMinutes((allTimes/(i+1))*(checkoutReqs.length-i));
            System.out.print(" | ETA: " + time + " mins left" );
        }
        writer.close();
        System.out.println("Finished Benchmark");
    }

    /*
    Methods to warm up during benchmarking,
    this should include the benchmarking method, but also teardown methods needed between invocations.
     */
    private static void warmUpBench() throws IOException {
        System.out.println("Warm Up not possible for checkout cart, " +
                "instead create more requests and trim them after benchmarks");
    }

    /*
    Method executed before every request
    */
    private static void requestPrep(int requestnumber){
        thisSite.invoke("Login", checkoutReqs[requestnumber][0],
                checkoutReqs[requestnumber][1]);
        thisSite.invoke("Search", checkoutReqs[requestnumber][2], false, 50);
        int numOfAdditions = Integer.parseInt(checkoutReqs[requestnumber][4]);
        for(int i = 0; i < numOfAdditions ; i++){
            thisSite.invoke("FromFoundAddToCart", i+1, 1);
        }
        double addBal = 110.00 * (double) numOfAdditions;
        thisSite.invoke("AddBalance", addBal, false);
    }

    /*
    The method that will be measured during benchmarking
     */
    private static boolean request(int requestnumber){
        //checkout
        return thisSite.invoke("Checkout", false);
    }

    /*
    Method executed after every request
     */
    private static void requestTeardown(){
        //LogOut
        thisSite.invoke("Logout");
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

    private static void eatObject(Object obj) throws IOException{
        try(ByteArrayOutputStream b = new ByteArrayOutputStream()){
            try(ObjectOutputStream o = new ObjectOutputStream(b)){
                o.writeObject(obj);
            }
            byte[] bArr = b.toByteArray();
            bh.write(bArr);
        }
    }
}
