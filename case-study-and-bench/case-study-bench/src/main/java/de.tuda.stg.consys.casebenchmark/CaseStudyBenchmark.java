package de.tuda.stg.consys.casebenchmark;

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
import java.util.LinkedList;
import java.util.Random;
import java.util.concurrent.TimeUnit;


//TODO: Throughput, latenz, gesamtlaufzeit einer methode unter load; Verschiedene Syncstrategien.

//TODO: Design and implement Benchmark locally
//TODO: Ideen von anderen papers klauen


@Warmup(iterations = 1)
@Measurement(iterations = 1)
@BenchmarkMode(Mode.SampleTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Fork(1)
public class CaseStudyBenchmark {


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
         * */

        @Param({"login", "register", "search", "addCart", "checkOut", "ViewProd", "AddBalance"})
        String endpoint;

        JReplicaSystem[] replicaSystems;

        JRef<@Strong Database> database;

        LinkedList<JRef<@Weak ShoppingSite>> sites;

        Random r = new Random();

        Blackhole bh = new Blackhole("");

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


        /*
            Function for setting up replica systems, //TODO: replace with code that works with AWS later
         */
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

        /*
            Function for setting up the database
         */
        private boolean setUpDatabase(int repSysNum){
            if(repSysNum < 0 || repSysNum >= replicaSystems.length){
                return false;
            }else {
                database = replicaSystems[repSysNum].replicate("database",
                        new Database(replicaSystems[repSysNum]), JConsistencyLevel.STRONG);
                return true;
            }
        }

        /*
            Function to set up shopping sites, through which measurements will be taken.
            One site for each replicasystem
         */
        private boolean setUpSites(){
            sites = new LinkedList<JRef<@Weak ShoppingSite>>();
            for (JReplicaSystem sys: replicaSystems) {
                sites.add(sys.replicate(new ShoppingSite(database), JConsistencyLevel.WEAK));
            }
            return true;
        }

        private boolean fillDatabase(){
            if(database != null){
                //Read products from pregenerated product file
                String[] products = ContentHandler.readFile("productsForBenchmark.txt");
                //If file is missing generate it
                if(products.length < 0){
                    products = ContentHandler.generateProducts(500);
                    ContentHandler.writeFile("productsForBenchmark.txt", products);
                }

                //Add products to database
                for (String prod: products) {
                    String[] split = prod.split(";");
                    database.invoke("AddProduct", split[0], split[1], replicaSystems[0]);
                }


                //Read users from pregenerated product file
                String[] users = ContentHandler.readFile("usersForBenchmark.txt");
                //If file is missing generate it
                if(users.length < 0){
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
                    database.invoke("AddUser", split[0], split[1], replicaSystems[0]);
                }
                return true;
            }
            else
                return false;
        }

        @Setup(Level.Iteration)
        public void systemSetup() throws Exception {
            /*
                If testing without load, only 2 replica systems, for test with load add a third
             */

            //Setup Replica Systems
            setUpReplicaSystems(2);

            //Setup Database on replica system 0
            setUpDatabase(0);
            fillDatabase();

            //Setup Shopping Site
            setUpSites();



            switch (endpoint){
                case "login":
                    String[] split = loginUsers[r.nextInt(loginUsers.length)].split(";");
                    currUserName = split[0]; currPassword = split[1];
                    break;
                case "register":
                    newUserName = "NewUserName" + registeredUsers;
                    newPassword = "Pass" + registeredUsers + r.nextInt();
                    registeredUsers++;
                    break;
                case "search":
                    currentSearchTerm = ContentHandler.searchableWords[r.nextInt(ContentHandler.searchableWords.length)];
                    break;
                case "addCart":
                    String search = ContentHandler.searchableWords[r.nextInt(ContentHandler.searchableWords.length)];
                    sites.get(1).invoke("Search", search);
                    addToCartIndex =
                            ((LinkedList<JRef<@Strong Product>>) sites.get(1).getField("FoundProducts"))
                                    .size()/2 + 1;
                    break;
                case "checkOut":
                    String[] split1 = loginUsers[r.nextInt(loginUsers.length)].split(";");
                    currUserName = split1[0]; currPassword = split1[1];
                    sites.get(1).invoke("Login", currUserName,
                            currPassword,replicaSystems[1]);
                    String search1 = ContentHandler.searchableWords[r.nextInt(ContentHandler.searchableWords.length)];
                    sites.get(1).invoke("Search", search1);
                    int midway = ((LinkedList<JRef<@Strong Product>>) sites.get(1).getField("FoundProducts"))
                            .size()/2 + 1;
                    for (int x = 1; x < midway;x++) {
                        sites.get(1).invoke("FromFoundAddToCart",
                                x, 5, replicaSystems[1]);
                    }
                    break;
                case "ViewProd":
                    String search2 = ContentHandler.searchableWords[r.nextInt(ContentHandler.searchableWords.length)];
                    sites.get(1).invoke("Search", search2);
                    displayInfoIndex =
                            ((LinkedList<JRef<@Strong Product>>) sites.get(1).getField("FoundProducts"))
                                    .size()/2 + 1;
                    break;
                case "AddBalance":
                    String[] split2 = loginUsers[r.nextInt(loginUsers.length)].split(";");
                    currUserName = split2[0]; currPassword = split2[1];
                    sites.get(1).invoke("Login", currUserName,
                            currPassword,replicaSystems[1]);
                    break;
            }

            Thread.sleep(1000);
        }

        @TearDown(Level.Invocation)
        public void postInvocation(){
            switch (endpoint){
                case "login":
                    //Log out after each login
                    sites.get(1).invoke("Logout", replicaSystems[1]);
                    break;
                case "register":
                    break;
                case "search":
                    break;
                case "addCart":

                    break;
                case "checkOut":
                    //Log out after checking out a cart
                    sites.get(1).invoke("Logout", replicaSystems[1]);
                    break;
                case "ViewProd":

                    break;
                case "AddBalance":
                    //Log out after adding balance
                    sites.get(1).invoke("Logout", replicaSystems[1]);
                    break;
            }
        }

        @TearDown(Level.Iteration)
        public void systemTeardown() throws Exception {
            for (JReplicaSystem system: replicaSystems) {
                system.close();
            }
        }
    }

    @Benchmark
    public void benchmarkRequest(BenchmarkSetup setup) {
        switch (setup.endpoint){
            case "login":
                //Login
                setup.bh.consume(setup.sites.get(1).invoke("Login", setup.currUserName,
                        setup.currPassword,setup.replicaSystems[1]));
                break;
            case "register":
                //Register new User from previously generated new unique user and password.
                setup.bh.consume(setup.sites.get(1).invoke("Register", setup.newUserName,
                        setup.newPassword, setup.replicaSystems[1]));
                break;
            case "search":
                //Search the products for a random search term, should return ~1/26 of all products
                setup.bh.consume(setup.sites.get(1).invoke("Search", setup.currentSearchTerm));
                break;
            case "addCart":
                //add a previously searched item
                setup.bh.consume(setup.sites.get(1).invoke("FromFoundAddToCart",
                        setup.addToCartIndex, 5, setup.replicaSystems[1]));
                break;
            case "checkOut":
                //checkout a previously filled shopping cart
                setup.bh.consume(setup.sites.get(1).invoke("Checkout", setup.replicaSystems[1]));
                break;
            case "ViewProd":
                //View a previously searched item
                setup.bh.consume(setup.sites.get(1).invoke("FromFoundDisplayInfo",
                        setup.displayInfoIndex, true));
                break;
            case "AddBalance":
                //Add balance for a certain user
                setup.bh.consume(setup.sites.get(1).invoke("AddBalance", 50,
                        setup.replicaSystems[1]));
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

}