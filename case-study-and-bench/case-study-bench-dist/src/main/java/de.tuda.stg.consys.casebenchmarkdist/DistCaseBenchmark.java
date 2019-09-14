package de.tuda.stg.consys.casebenchmarkdist;

import de.tuda.stg.consys.casestudy.Database;
import de.tuda.stg.consys.casestudy.Product;
import de.tuda.stg.consys.casestudy.ShoppingSite;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import org.openjdk.jmh.Main;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.io.*;
import java.util.*;
import java.util.concurrent.TimeUnit;


//TODO: Throughput, latenz, gesamtlaufzeit einer methode unter load; Verschiedene Syncstrategien.

//TODO: Design and implement Benchmark locally
//TODO: Ideen von anderen papers klauen

/**
 * THIS IS THE DISTRIBUTED BENCHMARK
 */
@Warmup(iterations = 1)
@Measurement(iterations = 1)
@BenchmarkMode(Mode.SampleTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Fork(1)
public class DistCaseBenchmark {

    public static void main(String[] args) throws Exception {
        Main.main(args);
    }

    @State(Scope.Benchmark)
    public static class BenchmarkSetup {

        /*
         * Endpoints to test:
         *  - Logging in
         *  - Registering a new User
         *  - Searching for Items
         *  - Adding Items to cart
         *  - Checking out
         *  - View Product info
         *  - Changing User Options (such as adding balance)
         *
         * Things to compare:
         * Case Study mit Strong auf allen werten vs fine grained
         * Vergleich incrementelle liste vs. Strong nicht distributed liste
         * */

        //@Param({"login", "register", "search", "addCart", "checkOut", "ViewProd", "AddBalance"})
        @Param({"login", "register", "search", "addCart", "checkOut", "ViewProd", "AddBalance"})
        String endpoint;

        JRef<@Strong Database> database;

        Random r = new Random();

        static JReplicaSystem thisSystem;

        JRef<@Weak ShoppingSite> thisSite;

        static JRef<@Strong BenchmarkCommunication> comChannel;
        //This replicas turn to run the benchmark
        static int thisRunInfo;
        //This replicas turn to setup the benchmark
        static int thisSetupInfo;
        //The total amount of systems involved
        static int totalSystemCount;

        /**
         * INFO FOR ENDPOINTS:
         */
        //Logins for login Endpoint
        String[] loginUsers = new String[10];
        String currUserName; String currPassword;
        //New Login for register
        String newUserName; String newPassword; int registeredUsers = 0;
        //Randomly chosen search term
        String currentSearchTerm;
        //Item to add to cart from previously found items
        int addToCartIndex;
        //Item to fetch info for from previously found items
        int displayInfoIndex;

        public static void readHostFile() throws Exception{
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
            String path = "hosts.txt";
            String currLine;
            LinkedList<String> fileCont = new LinkedList<>();

            try {
                FileReader fileReader =
                        new FileReader(path);

                BufferedReader bufferedReader =
                        new BufferedReader(fileReader);

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
            catch(IOException ex) {
                System.out.println(
                        "Error reading host file");
                System.exit(0);
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
            comChannel.setField("benchmarkInstanceLocation", thisHost);
            comChannel.setField("benchmarkInstanceOnline", true);
            while(!(boolean) comChannel.invoke("confirmReady")){
                comChannel.setField("msg", "Hello this is the benchmark");
                comChannel.invoke("setReady", thisRunInfo);
                System.out.println("Not all systems ready yet, waiting for them to connect...");
                Thread.sleep(2000);
            }

        }


        /**
         * Function for the running benchmark instance to request the setup instance to setup the database and sites.
         */
        private void requestSetup() throws InterruptedException {
            while(!((boolean) comChannel.getField("setupInstanceReady"))){
                comChannel.setField("requestInstanceSetup", true);
                Thread.sleep(2000);
            }
            database = thisSystem.ref("database", Database.class, JConsistencyLevel.STRONG);
            thisSite = thisSystem.replicate(new ShoppingSite(database), JConsistencyLevel.WEAK);
            comChannel.setField("setupInstanceReady", false);
            loginUsers = comChannel.getField("loginUsers");
        }

        @Setup(Level.Iteration)
        public void systemSetup() throws Exception {

            //Connect the benchmark system to the other systems
            readHostFile();

            //Request Setup from the replica system responsible for setup
            requestSetup();

            switch (endpoint){
                case "login":
                    String[] split = loginUsers[r.nextInt(loginUsers.length)].split(";");
                    currUserName = split[0]; currPassword = split[1];
                    break;
                case "register":
                    break;
                case "search":
                    currentSearchTerm = ContentHandler.searchableWords[r.nextInt(ContentHandler.searchableWords.length)];
                    break;
                case "addCart":
                    String search = ContentHandler.searchableWords[r.nextInt(ContentHandler.searchableWords.length)];
                    thisSite.invoke("Search", search, false);
                    addToCartIndex =
                            ((LinkedList<JRef<@Strong Product>>) thisSite.getField("FoundProducts"))
                                    .size()/2 + 1;
                    break;
                case "checkOut":
                    String[] split3 = loginUsers[r.nextInt(loginUsers.length)].split(";");
                    currUserName = split3[0]; currPassword = split3[1];
                    thisSite.invoke("Login", currUserName,
                            currPassword);
                    String search1 = ContentHandler.searchableWords[r.nextInt(ContentHandler.searchableWords.length)];
                    thisSite.invoke("Search", search1, false);
                    break;
                case "ViewProd":
                    String search2 = ContentHandler.searchableWords[r.nextInt(ContentHandler.searchableWords.length)];
                    thisSite.invoke("Search", search2, false);
                    displayInfoIndex =
                            ((LinkedList<JRef<@Strong Product>>) thisSite.getField("FoundProducts"))
                                    .size()/2 + 1;
                    break;
                case "AddBalance":

                    break;
            }

            Thread.sleep(1000);
        }

        @Setup(Level.Invocation)
        public void preInvocation(){
            switch (endpoint){
                case "login":
                    break;
                case "register":
                    newUserName = "NewUserName" + registeredUsers;
                    newPassword = "Pass" + registeredUsers + r.nextInt();
                    registeredUsers++;
                    break;
                case "search":

                    break;
                case "addCart":
                    //Log in before adding things to the cart
                    String[] split1 = loginUsers[r.nextInt(loginUsers.length)].split(";");
                    thisSite.invoke("Login", split1[0],
                            split1[1]);
                    break;
                case "checkOut":
                    int midway = ((LinkedList<JRef<@Strong Product>>) thisSite.getField("FoundProducts"))
                            .size()/2 + 1;
                    thisSite.invoke("AddBalance", 5000.0, false);
                    thisSite.invoke("FromFoundAddToCart", midway, 5);
                    break;
                case "ViewProd":

                    break;
                case "AddBalance":
                    String[] split2 = loginUsers[r.nextInt(loginUsers.length)].split(";");
                    currUserName = split2[0]; currPassword = split2[1];
                    thisSite.invoke("Login", currUserName,
                            currPassword);
                    break;
            }
        }

        @TearDown(Level.Invocation)
        public void postInvocation(){
            switch (endpoint){
                case "login":
                    //Log out after each login
                    thisSite.invoke("Logout");
                    break;
                case "register":
                    //Log out after each new registration
                    thisSite.invoke("Logout");
                    break;
                case "search":
                    break;
                case "addCart":
                    //Log out after having added things to the cart
                    thisSite.invoke("Logout");
                    break;
                case "checkOut":

                    break;
                case "ViewProd":

                    break;
                case "AddBalance":
                    //Log out after adding balance
                    thisSite.invoke("Logout");
                    break;
            }
        }

        @TearDown(Level.Iteration)
        public void systemTeardown() throws Exception {
            if(endpoint.equals("checkOut"))
                thisSite.invoke("Logout");

            comChannel.setField("requestDBteardown", true);
            comChannel.setField("benchmarkInstanceOnline", false);
            thisSystem.close();
        }
    }

    @Benchmark
    public void benchmarkRequest(BenchmarkSetup setup, Blackhole bh) {
        switch (setup.endpoint){
            case "login":
                //Login
                bh.consume(setup.thisSite.invoke("Login", setup.currUserName,
                                    setup.currPassword));
                break;
            case "register":
                //Register new User from previously generated new unique user and password.
                bh.consume(setup.thisSite.invoke("RegisterNewUser", setup.newUserName,
                        setup.newPassword));
                break;
            case "search":
                //Search the products for a random search term, should return ~1/26 of all products
                bh.consume(setup.thisSite.invoke("Search", setup.currentSearchTerm, false));
                break;
            case "addCart":
                //add a previously searched item
                //TODO: FIX THIS
                bh.consume(setup.thisSite.invoke("FromFoundAddToCart",
                        setup.addToCartIndex, 5));
                break;
            case "checkOut":
                //checkout a previously filled shopping cart
                bh.consume(setup.thisSite.invoke("Checkout",  false));
                break;
            case "ViewProd":
                //View a previously searched item
                bh.consume(setup.thisSite.invoke("FromFoundDisplayInfo",
                        setup.displayInfoIndex, true, false));
                break;
            case "AddBalance":
                //Add balance for a certain user
                bh.consume(setup.thisSite.invoke("AddBalance", 50.0, false));
                break;
        }
    }
}