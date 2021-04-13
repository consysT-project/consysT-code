package de.tuda.stg.consys.examples.auctions;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

import java.io.IOException;
import java.util.List;

public class TestSystem {

    static long time;
    static JReplicaSystem replicaSystem1;
    static JReplicaSystem replicaSystem2;

    public static void main(String... args) throws Exception {
        /*

        Test numbers:
        1:TestNoWrapper
        2:TestStrongWrapper
        3:TestWeakToStrong
        4:TestCreateBidSubSys
        5:TestCreateBidSubSysOnMain
         */


        replicaSystem1 = Replicas.replicaSystem1;
        replicaSystem2 = Replicas.replicaSystem2;

        //TestReplicas();
        TestCreateBidSubSys(replicaSystem1, replicaSystem2);
        System.out.println("Test done!");
        try {
            replicaSystem2.close();
            replicaSystem1.close();

            initializeSystems();
            //Replicas.replicaSystem1.close();
            //Replicas.replicaSystem2.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
        TestCreateBidSubSys(replicaSystem1, replicaSystem2);

        //replicaSystem1.addReplicaSystem("127.0.0.1", 2552);
        //replicaSystem2.addReplicaSystem("127.0.0.1", 2553);
        //RunTest(1, true);
        //System.out.println("Test done!");
        //TestCreateBidSubSys();

        //Warmup
        //Warmup();
        //Warmup();


        //FullTest(1, false, false, false, true, true);



    }


    private static void initializeSystems() {
        JReplicaSystem[] systems = JReplicaSystems.fromActorSystemForTesting(2);
        replicaSystem1 = systems[0];
        replicaSystem2 = systems[1];
    }

    public static  void FullTest(int n, boolean t1, boolean t2, boolean t3, boolean t4, boolean t5){
        //n -> Anzahl der durchläufe für die Berechnung der Durchschnittszeit


        float avg1 = 0;
        float avg2 = 0;
        float avg3 = 0;
        float avg4 = 0;
        float avg5 = 0;



        for(int i = 0; i < n; i++){

            if(false){
                initializeSystems();
            }

            //test on one auctioneer with everything strongly consistent;
            if(t1)avg1 += RunTest(1, true);

            //Test with wrapper for functions that require strong consistency
            if(t2)avg2 += RunTest(2, true);

            //Test with 3 struktures
            if(t3)avg3 += RunTest(3, true);

            //Test with 3 struktures
            //Test Bid subsystem
            if(t4)avg4 += RunTest(4, true);

            //Test Bid subsystem on Main
            if(t5)avg5 += RunTest(5, true);

        }

        if(t1)System.out.println("Test 1 took " + avg1 / n + " seconds on average to complete");

        if(t2)System.out.println("Test 2 took " + avg2 / n + " seconds on average to complete");

        if(t3)System.out.println("Test 3 took " + avg3 / n + " seconds on average to complete");

        if(t4)System.out.println("Test 4 took " + avg4 / n + " seconds on average to complete");

        if(t5)System.out.println("Test 5 took " + avg5 / n + " seconds on average to complete");


    }

    public static float RunTest(int nr, final boolean timer){
        float duration = 0;
        long finalTime;



        System.out.println("Test " + nr);

        if(timer){
            time = System.currentTimeMillis();
        }

        switch (nr){
            case 1:
                TestNoWrapper();
                break;
            case 2:
                TestStrongWrapper();
                break;
            case 3:
                TestWeakToStrong();
                break;
            case 4:
                TestCreateBidSubSys(replicaSystem1, replicaSystem2);
                break;
            case 5:
                TestCreateBidSubSysOnMain();
                break;
        }

        if(timer){
            finalTime = System.currentTimeMillis();
            duration = (int)finalTime - (int)time;
            duration = duration  / 1000;

        }



        try {
            System.out.println("Press enter to start next test");
            System.in.read();
        } catch (IOException e) {
            e.printStackTrace();
        }
        return duration;
    }

    public static void Warmup(){
        RunTest(1, false);
        RunTest(2, false);
        RunTest(3, false);
        RunTest(4, false);
    }

    public static void TestReplicas(){


        //replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
        //replicaSystem2 = JReplicaSystem.fromActorSystem(2553);
    }




    public static void TestCreateBidSubSys(JReplicaSystem sys1, JReplicaSystem sys2){
        //Create Auction System
        T4StrongSys system = new T4StrongSys(); //Replicate?

        //Bid system placeholders

        JRef<@Weak T4BidSystem> bidSys1;
        JRef<@Weak T4BidSystem> bidSys2;

        //Create Users on strong system
        // -> Users can only participate at auctions if they exist when the auction is started

        Client tom = system.RegisterUser("Tom");
        Client peter = system.RegisterUser("Peter");
        Client alice = system.RegisterUser("Alice");

        //Starting auction
        System.out.println("Starting Auction");
        system.StartAuction(sys1, sys2);


        bidSys1 = system.GetBidSys(1);
        bidSys2 = system.GetBidSys(2);

        if(bidSys1 == null)System.out.println("BidSys 1 not found");
        List<Client> clients = bidSys1.getField("registeredUsers");
        for (Client c: clients) {
            System.out.println("Client: " + c.getName() + " - id: " + c.getClientID());
        }
        //if(clients.contains(tom))System.out.println("Id: " + tom.getClientID() + " found");

        //System.out.println("Starting to bid");

        boolean b1, b2;

        try {
            bidSys2.getField("enabled");
        }
        catch (Exception e){
            e.printStackTrace();
        }
        try{
            if(bidSys1.invoke("Bid", new Bid(tom.getClientID(), 5)))System.out.println("Bid placed");
            if(bidSys2.invoke("Bid", new Bid(alice.getClientID(), 8)))System.out.println("Bid placed");
            if(bidSys1.invoke("Bid", new Bid(peter.getClientID(), 6)))System.out.println("Bid placed");
            if(bidSys2.invoke("Bid", new Bid(tom.getClientID(), 7)))System.out.println("Bid placed");

        }catch (Exception e){
            System.out.println("Error placing bid!");
        }



        //Stopping auction
        system.StopAuction();


        //Bidding should not be possible at this point

        try{
            if(bidSys1.invoke("Bid", new Bid(peter.getClientID(), 12)))System.out.println("Bid placed");
            else System.out.println("Failed to place bid");
            if(bidSys2.invoke("Bid", new Bid(tom.getClientID(), 1)))System.out.println("Bid placed");
            else System.out.println("Failed to place bid");

        }catch (Exception e){
            System.out.println("Error placing bid!");
        }

        int winner = system.CloseAuction();
        if(winner == 0)System.out.println("No winner was declared!");
        else System.out.println("The winner is: " + system.GetClient(winner).getName());


        //System.out.println("Created " + client.getName() + " with ID: " + client.getClientID());

    }
    public static void TestStrongWrapper(){
        //Testing:
        //Bid on weak auctioneer
        //Start and Closing of the Auction are done through a Strong wrapper

        //T1Auctioneer plus replica
        JRef<@Weak T2WeakSubAuct> auct1 = replicaSystem1.replicate("auctioneer2", new T2WeakSubAuct(), JConsistencyLevels.WEAK);
        JRef<@Weak T2WeakSubAuct> auct2 = replicaSystem2.lookup("auctioneer2", (Class<@Weak T2WeakSubAuct>) T2WeakSubAuct.class, JConsistencyLevels.WEAK);

        //Strong Wrapper to start/stop the auction and register new users
        JRef<@Strong T2StrongAuctSys> wrapper1 = replicaSystem1.replicate("auctionWrapper", new T2StrongAuctSys(auct1), JConsistencyLevels.STRONG);
        JRef<@Strong T2StrongAuctSys> wrapper2 = replicaSystem2.lookup("auctionWrapper", (Class<@Strong T2StrongAuctSys>) T2StrongAuctSys.class, JConsistencyLevels.STRONG);

        System.out.println("Registering users");

        Client c1 = wrapper1.invoke("RegisterUser", "hans");
        Client hansFail = wrapper2.invoke("RegisterUser", "hans");
        Client c2 = wrapper2.invoke("RegisterUser", "peter");


        System.out.println("Starting Auction");

        //Starting Auction on wrapper 1
        wrapper1.invoke("StartAuction");
        //Starting Auction on wrapper 2 -> expecting failure
        //wrapper2.invoke("StartAuction");

        auct2.sync();


        System.out.println("Placing bids");
        //Place Bids
        auct1.invoke("PlaceBid", c1.getClientID(), 2);

        auct2.invoke("PlaceBid", c2.getClientID(), 3);

        auct1.invoke("PlaceBid", 5, 4);//Not registered -> expecting failure

        auct2.invoke("PlaceBid", c1.getClientID(), 5);

        wrapper1.invoke("StopAuction");

        auct2.sync();

        auct1.invoke("PlaceBid", c2.getClientID(), 7);

        System.out.println("The winner is: " + wrapper2.invoke("CloseAuction"));

        auct2.invoke("PlaceBid", c1.getClientID(), 8);

        auct1.invoke("ShowBids");

    }

    private static void TestNoWrapper(){
        JRef<@Strong T1Auctioneer> auctioneer1 = Replicas.replicaSystem1.replicate("auctioneer", new T1Auctioneer(), JConsistencyLevels.WEAK);
        JRef<@Strong T1Auctioneer> auctioneer2 = Replicas.replicaSystem2.lookup("auctioneer", (Class<@Weak T1Auctioneer>) T1Auctioneer.class, JConsistencyLevels.WEAK);

        Client c1 = auctioneer1.invoke("RegisterUser", "hans");
        Client cTest = auctioneer1.invoke("RegisterUser", "hans");
        Client c2 = auctioneer1.invoke("RegisterUser", "peter");

        auctioneer1.invoke("StartAuction");
        auctioneer2.invoke("PlaceBid", c1.getClientID(), 2);

        auctioneer2.invoke("PlaceBid", c2.getClientID(), 3);

        auctioneer2.invoke("PlaceBid", 5, 4);

        auctioneer2.invoke("PlaceBid", c1.getClientID(), 5);

        auctioneer2.sync();

        System.out.println("The winner is: " + auctioneer2.invoke("CloseAuction"));

        auctioneer2.invoke("PlaceBid", c2.getClientID(), 7);

        auctioneer2.invoke("PlaceBid", c1.getClientID(), 8);
        auctioneer2.sync();

        auctioneer1.invoke("ShowBids");

        if(false){
            try {
                replicaSystem2.close();
                replicaSystem1.close();
            } catch (Exception e) {
                e.printStackTrace();
            }
        }

    }

    private static void TestWeakToStrong(){
        //Testing:
        //Bid on weak wrapper
        //Start and Closing of the Auction are done through a Strong sub system

        //Strong sub system
        JRef<@Strong T3SubSystemStrong> subSyst1 = Replicas.replicaSystem1.replicate("auctionWrapper", new T3SubSystemStrong(), JConsistencyLevels.STRONG);
        JRef<@Strong T3SubSystemStrong> subSyst2 = Replicas.replicaSystem2.lookup("auctionWrapper", (Class<@Strong T3SubSystemStrong>) T3SubSystemStrong.class, JConsistencyLevels.STRONG);

        //Wrapper
        JRef<@Weak T3WeakBidSystem> weakWrap1 = Replicas.replicaSystem1.replicate("auctioneer2", new T3WeakBidSystem(subSyst1), JConsistencyLevels.WEAK);
        JRef<@Weak T3WeakBidSystem> weakWrap2 = Replicas.replicaSystem2.lookup("auctioneer2", (Class<@Weak T3WeakBidSystem>) T3WeakBidSystem.class, JConsistencyLevels.WEAK);

        System.out.println("Registering users");

        Client c1 = weakWrap1.invoke("RegisterUser", "hans");
        Client hansFail = weakWrap2.invoke("RegisterUser", "hans");
        Client c2 = weakWrap2.invoke("RegisterUser", "peter");


        System.out.println("Starting Auction");

        //Starting Auction on wrapper 1
        weakWrap1.invoke("StartAuction");
        //Starting Auction on wrapper 2 -> expecting failure
        weakWrap2.invoke("StartAuction");

        //auct2.sync();


        System.out.println("Placing bids");
        //Place Bids
        weakWrap1.invoke("AddBid", c1.getClientID(), 2);

        weakWrap2.invoke("AddBid", c2.getClientID(), 3);

        weakWrap1.invoke("AddBid", 5, 4);//Not registered -> expecting failure

        weakWrap2.invoke("AddBid", c1.getClientID(), 5);

        weakWrap1.invoke("StopAuction");

        //auct2.sync();

        weakWrap1.invoke("AddBid", c2.getClientID(), 7);

        System.out.println("The winner is: " + weakWrap2.invoke("CloseAuction"));

        weakWrap2.invoke("AddBid", c1.getClientID(), 8);

        //weakWrap1.invoke("ShowBids");

    }

    public static void TestCreateBidSubSysOnMain(){
        //Create Auction System
        T5StrongSys system = new T5StrongSys(); //Replicate?

        //Bid system placeholders


        //Create Users on strong system
        // -> Users can only participate at auctions if they exist when the auction is started

        Client tom = system.RegisterUser("Tom");
        Client peter = system.RegisterUser("Peter");
        Client alice = system.RegisterUser("Alice");

        //Starting auction
        System.out.println("Starting Auction");

        JRef<@Weak T5BidSystemOnMain> bidSys1 = replicaSystem1.replicate("bidSys1", new T5BidSystemOnMain(system.registeredUsers), JConsistencyLevels.WEAK);
        JRef<@Weak T5BidSystemOnMain> bidSys2 = replicaSystem2.lookup("bidSys1", (Class<@Weak T5BidSystemOnMain>) T5BidSystemOnMain.class, JConsistencyLevels.WEAK);
        system.StartAuction(bidSys1, bidSys2);


        bidSys1 = system.GetBidSys(1);
        bidSys2 = system.GetBidSys(2);

        if(bidSys1 == null)System.out.println("BidSys 1 not found");
        List<Client> clients = bidSys1.getField("registeredUsers");
        for (Client c: clients) {
            System.out.println("Client: " + c.getName() + " - id: " + c.getClientID());
        }
        //if(clients.contains(tom))System.out.println("Id: " + tom.getClientID() + " found");

        //System.out.println("Starting to bid");

        boolean b1, b2;

        try {
            bidSys2.getField("enabled");
        }
        catch (Exception e){
            e.printStackTrace();
        }
        try{
            if(bidSys1.invoke("Bid", new Bid(tom.getClientID(), 5)))System.out.println("Bid placed");
            if(bidSys2.invoke("Bid", new Bid(alice.getClientID(), 8)))System.out.println("Bid placed");
            if(bidSys1.invoke("Bid", new Bid(peter.getClientID(), 6)))System.out.println("Bid placed");
            if(bidSys2.invoke("Bid", new Bid(tom.getClientID(), 7)))System.out.println("Bid placed");

        }catch (Exception e){
            System.out.println("Error placing bid!");
        }



        //Stopping auction
        system.StopAuction();


        //Bidding should not be possible at this point

        try{
            if(bidSys1.invoke("Bid", new Bid(peter.getClientID(), 12)))System.out.println("Bid placed");
            else System.out.println("Failed to place bid");
            if(bidSys2.invoke("Bid", new Bid(tom.getClientID(), 1)))System.out.println("Bid placed");
            else System.out.println("Failed to place bid");

        }catch (Exception e){
            System.out.println("Error placing bid!");
        }

        int winner = system.CloseAuction();
        if(winner == 0)System.out.println("No winner was declared!");
        else System.out.println("The winner is: " + system.GetClient(winner).getName());


        //System.out.println("Created " + client.getName() + " with ID: " + client.getClientID());

    }

}
