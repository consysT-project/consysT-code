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

        //JReplicaSystem[] replicaSystems;

        JRef<@Strong Database> database;

        LinkedList<JRef<@Weak ShoppingSite>> sites;

        Random r = new Random();


        static JReplicaSystem thisSystem;

        JRef<@Weak ShoppingSite> thisSite;

        static JRef<@Strong benchmarkCommunication> comChannel;
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
                comChannel = thisSystem.replicate("valueString", new benchmarkCommunication(totalSystemCount), JConsistencyLevel.STRONG);
                System.out.println("Successfully established communication channel");
            }catch (Exception e){
                System.out.println("Communication Channel has already been established");
                comChannel = thisSystem.ref("valueString", benchmarkCommunication.class, JConsistencyLevel.STRONG);
            }

            comChannel.invoke("setReady", thisRunInfo);
            while(!(boolean) comChannel.invoke("confirmReady")){
                System.out.println("Not all systems ready yet, waiting for them to connect...");
                Thread.sleep(2000);
            }

        }


        /*
            Function for setting up replica systems,

        private void setUpReplicaSystems(int systemCount){
            replicaSystems = new JReplicaSystem[systemCount];

            for (int i = 0; i < systemCount; i++) {
                replicaSystems[i] = JReplicaSystem.fromActorSystem(2552 + i);
            }

            for (int i = 0; i < systemCount; i++) {
                for (int j = 0; j < systemCount; j++) {
                    if (i != j)
                        replicaSystems[i].addReplicaSystem("127.0.0.1", 2552 + j);
                }
            }
        }
        */

        /*
            Function for setting up the database
         */
        private boolean setUpDatabase(){
            database = thisSystem.replicate("database",
                    new Database(), JConsistencyLevel.STRONG);
            return database.invoke("init");
        }

        private boolean fillDatabase(){
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
        }

        @Setup(Level.Trial)
        public void connectReplicas() throws Exception {
            //Connect all replicas
            readHostFile();

            if((int) comChannel.getField("benchmarkTurn") == thisRunInfo){
                    //&& (boolean) comChannel.getField("finishedRunning")
                //Its this replicas turn to run
            }
            else {
                while ((int) comChannel.getField("benchmarkTurn") != thisRunInfo){
                    //its not this replicas turn to run

                    //its this replicas turn to setup the database
                    while ((int) comChannel.getField("benchmarkTurn") == thisSetupInfo){
                        if(comChannel.getField("requestInstanceSetup")){
                            //Setup Database on this replica system
                            setUpDatabase();
                            fillDatabase();
                        }

                        Thread.sleep(2000);
                    }

                    //Add code for instance that changes values here

                    Thread.sleep(2000);
                }

            }

        }

        @TearDown(Level.Trial)
        public void disconnectReplicas() throws Exception{
            //Increment the benchmark turn value
            comChannel.setField("benchmarkTurn", (int) comChannel.getField("benchmarkTurn") + 1 );

            while(!(boolean) comChannel.invoke("allDone")){
                //its this replicas turn to setup the database
                while ((int) comChannel.getField("benchmarkTurn") == thisSetupInfo){
                    if(comChannel.getField("requestInstanceSetup")){
                        //Setup Database on this replica system
                        setUpDatabase();
                        fillDatabase();
                    }

                    Thread.sleep(2000);
                }


                //Add code for instance that changes values here

                Thread.sleep(2000);
            }

            thisSystem.close();
        }

        @Setup(Level.Iteration)
        public void systemSetup() throws Exception {
            /*
                If testing without load, only 2 replica systems, for test with load add a third
             */
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

            //TODO: Replace with code that removes the database reference
            /*
            for (JReplicaSystem system: replicaSystems) {
                system.close();
            }
             */
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

    /**
     * A class for importing, exporting and generating content needed to fill the case study for the benchmark.
     */
    static class ContentHandler{


        public static String[] searchableWords = {"Alfa", "Bravo", "Charlie", "Delta", "Echo", "Foxtrot", "Golf",
                "Hotel", "India", "Juliett", "Kilo", "Lima", "Mike", "November", "Oscar", "Papa", "Quebec", "Romeo",
                "Sierra", "Tango", "Uniform", "Victor", "Whiskey", "Xray", "Yankee", "Zulu"};

        static public String[] readFile(String filename){
            String currLine = null;
            LinkedList<String> retList = new LinkedList<String>();

            try {
                FileReader fileReader =
                        new FileReader(filename);

                BufferedReader bufferedReader =
                        new BufferedReader(fileReader);

                while((currLine = bufferedReader.readLine()) != null) {
                    retList.add(currLine);
                }

                bufferedReader.close();
            }
            catch(FileNotFoundException ex) {
                System.out.println(
                        "Unable to open file '" +
                                filename + "'");
            }
            catch(IOException ex) {
                System.out.println(
                        "Error reading file '"
                                + filename + "'");
            }

            return retList.toArray(new String[retList.size()]);
        }

        static public boolean writeFile(String filename, String[] content){
            try {
                FileWriter fileWriter =
                        new FileWriter(filename);

                BufferedWriter bufferedWriter =
                        new BufferedWriter(fileWriter);

                for (String currLine: content) {
                    bufferedWriter.write(currLine);
                    bufferedWriter.newLine();
                }
                bufferedWriter.close();
                return true;
            }
            catch(IOException ex) {
                System.out.println(
                        "Error writing to file '"
                                + filename + "'");
                return false;
            }
        }

        static public String[] generateProducts(int count){
            Random r = new Random();
            String[] retArray = new String[count];
            for (int i = 0; i < count; i++){
                double price =  ((100 + r.nextInt(99900))/100);
                //Add one random searchable word to the products
                retArray[i] = new String("ProductName" + i + searchableWords[r.nextInt(searchableWords.length)] +
                        ";" + price);
            }
            return retArray;
        }

        static public String[] generateUsers(int count){
            Random r = new Random();
            String[] retArray = new String[count];
            for (int i = 0; i < count; i++){
                String pass = "";
                for(int j = 0; j < 6; j++){
                    pass += (char) (r.nextInt(26) + 'a');
                }
                pass += r.nextInt(1000);
                retArray[i] = new String("User" + i + ";" + pass);
            }
            return retArray;
        }
    }

    /**
     * A class for figuring out everything related to connecting replica systems
     * and figuring out which one is supposed to do what when.
     */
    static class RemoteConnector{
        //TODO: Add method to communicate on startup, to ensure all replica systems where correctly initialized
        //TODO: change the python script to include new layout of host file
        //TODO: Figure out how to run benchmark on one instance while it waits on the other, possibly through the same
        //channel needed for communicating readiness

        static String thisHost;

        static JReplicaSystem thisSystem;

        static JRef<@Strong Container> value;




        private static void setValue(){
            try{
                value = thisSystem.replicate("valueString", new Container("from " + thisHost), JConsistencyLevel.STRONG);

            }catch (Exception e){
                value = thisSystem.ref("valueString", Container.class, JConsistencyLevel.STRONG);
            }
        }

        static class Container implements Serializable{
            public String content;

            public Container(String cont){
                content = cont;
            }
        }
    }

    static class benchmarkCommunication{
        //An integer to indicate which replica systems turn it currently is to run the benchmark
        public int benchmarkTurn;
        //A boolean indicating if the benchmark finished running, is set on benchmark teardown
        //public boolean finishedRunning;
        //An array used for each replica system to indicate if they are finished setting up
        public boolean[] statusReport;
        //A boolean indicating if the system responsible for setup finished setup
        public boolean setupInstanceReady;
        //A boolean indicating that the system responsible for running is requesting a setup from the setup instance
        public boolean requestInstanceSetup;

        private int total;

        benchmarkCommunication(int totalCount){
            statusReport = new boolean[totalCount];
            //finishedRunning = true;
            total = totalCount;
            benchmarkTurn = 1;
            setupInstanceReady = false;
            requestInstanceSetup = false;
        }

        public void setReady(int orderInfo){
            statusReport[orderInfo - 1] = true;
        }

        //A function that returns if all replica systems are ready
        public boolean confirmReady(){
            for (boolean val:statusReport) {
                if(!val)
                    return val;
            }
            return true;
        }

        public boolean allDone(){
            return (benchmarkTurn > total);
        }
    }
}