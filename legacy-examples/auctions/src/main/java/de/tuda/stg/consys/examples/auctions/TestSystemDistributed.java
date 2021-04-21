package de.tuda.stg.consys.examples.auctions;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.store.utils.Address;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;
import de.tuda.stg.consys.japi.legacy.impl.akka.JAkkaReplicaSystem;

import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.Random;

public class TestSystemDistributed {

    static Random random;
    static long time;
    static JAkkaReplicaSystem sys;

    static int[] sysBids = new int[6];
    static int sysNr;

    public static void main(String... args) throws Exception{
        /*
        Test numbers:
        1:TestNoWrapper
        2:TestStrongWrapper
        3:TestWeakToStrong
        4:TestCreateBidSubSys
        5:TestCreateBidSubSysOnMain

         */

        /*TEST ABFOLGE:
        2 Random bid sequenzen (fur die beiden systeme) für alle tests gleich (aus vergleichs gründen)
        System 1:
        registriert 2 user (Hans, Peter)
        wartet (1Sekunde)
        startet auktion
        bid sequenz 1
        wartet bis auktionszeit (5 sekunden ) rum ist
        stoppt auktion
        bestimmt gewinner
        System 2:
        registriert 2 user + 1 user der dem ersten system gleicht (Alice, Bob, Peter)
        wartet auf auktionsstart
        bid sequenz 2
        wartet auf auktionsende
        bestimmt gewinner
        -------------------------
        Bids:
        Sys1:user 1 -> user 2 -> user 1 -> user 2
        Sys2:user 1 -> user 2 -> user 3 -> user 1 -> user 2 -> user 3
        */
            try {

            if (args[0].equals("0")) {
                sysNr = 0;
            } else if (args[0].equals("1")) {
                sysNr = 1;
            }
        }catch(Exception e){
            System.out.println( getCurrentTimeStamp() +" No arguments given");
            return;
        }



        int max = 100;
        int min = 5;

        //Bidding Sequenz wird generiert
        for(int i = 0; i < 6; i++){;
            //(Math.random() * (max - mid)) + min -> Upper bound not included | Returns number [min; max]
            sysBids[i] = (int) ((Math.random() * (max - min)) + min);
            System.out.println( getCurrentTimeStamp() +" Bid " + sysBids[i]);
        }


        //Warmup();//Lässt alle Tests einmal durchlaufen

        //RunTest(1, false);

        RunTest(2, true);
        //RunTest(3, false);

        System.out.println( getCurrentTimeStamp() +" Done!");

    }
    //Schließt die Replicas
    public static void ResetReplicas(){
            System.out.println(getCurrentTimeStamp() + " closing sys " + sysNr);
            try {
                sys.close();
            } catch (Exception e) {
                e.printStackTrace();
            }
    }

    //Erzeugt die Replicas auf dem jeweiligen Port
    private static void initializeSystems() {
        System.out.println(getCurrentTimeStamp() + " initializing " + sysNr);
        int port = 10000;
        if(sysNr == 0) port = 3344;
        else if(sysNr == 1) port = 3345;
        sys = JReplicaSystems.fromActorSystem(
                new Address("127.0.0.1", port),
                Arrays.asList(new Address("127.0.0.1", 3344), new Address("127.0.0.1", 3345))
        );
    }
    //Veraltet
    public static  void FullTest(int n, boolean t1, boolean t2, boolean t3, boolean t4, boolean t5) throws Exception{
        //n -> Anzahl der durchläufe für die Berechnung der Durchschnittszeit

        float avg1 = 0;
        float avg2 = 0;
        float avg3 = 0;
        float avg4 = 0;
        float avg5 = 0;


        for(int i = 0; i < n; i++){


            //test on one auctioneer with everything strongly consistent;
            if(t1)avg1 += RunTest(1, true);

            //Test with wrapper for functions that require strong consistency
            if(t2)avg2 += RunTest(2, true);

            //Test with 3 struktures
            if(t3)avg3 += RunTest(3, true);

            //Test Bid subsystem
            if(t4)avg4 += RunTest(4, true);

            //Test Bid subsystem on Main
            if(t5)avg5 += RunTest(5, true);

        }
        System.out.println( getCurrentTimeStamp() +"Testing done. Each test was run " +  n + " times.");
        if(t1)System.out.println( getCurrentTimeStamp() +"Test 1 took " + avg1 / n + " seconds on average to complete");

        if(t2)System.out.println( getCurrentTimeStamp() +"Test 2 took " + avg2 / n + " seconds on average to complete");

        if(t3)System.out.println( getCurrentTimeStamp() +"Test 3 took " + avg3 / n + " seconds on average to complete");

        if(t4)System.out.println( getCurrentTimeStamp() +"Test 4 took " + avg4 / n + " seconds on average to complete");

        if(t5)System.out.println( getCurrentTimeStamp() +"Test 5 took " + avg5 / n + " seconds on average to complete");


    }

    //Gibt einen String mit der Aktuellen Uhrzeit im Format HH:MM::SS zurück
    public static String getCurrentTimeStamp() {
        SimpleDateFormat sdfDate = new SimpleDateFormat("HH:mm:ss");//dd/MM/yyyy
        Date now = new Date();
        String strDate = sdfDate.format(now);
        return strDate;
    }

    //Lässt einen Test durchlaufen mit der Möglichekit ihn zu Timen.
    public static float RunTest(int nr, final boolean timer) throws Exception{
        //Runs the specified Test
        //Initializing replicas is included in Timer measurement
        System.out.println( getCurrentTimeStamp() +"Test " + nr);

        float duration = 0;
        long finalTime;



        if(timer){
            time = System.currentTimeMillis();
        }
        long waitedTime = 0;
        initializeSystems();

        switch (nr){
            case 1:
                waitedTime = TestNoWrapper();
                break;
            case 2:
                waitedTime = TestStrongWrapper();
                break;
            case 3:
                waitedTime = TestWeakToStrong();
                break;
            case 4:
                waitedTime = TestCreateBidSubSys();
                break;
            case 5:
                System.out.println( getCurrentTimeStamp() +"No test 5 available");
                //TestCreateBidSubSysOnMain();
                break;
        }

        if(timer){
            finalTime = System.currentTimeMillis();
            duration = (int)finalTime - (int)time;
            duration = duration  / 1000;
            waitedTime = waitedTime / 1000;
            System.out.println( getCurrentTimeStamp() +"The test took: " + duration + " seconds. The test waited internally for " + waitedTime + " seconds. Final time without waiting: " + (duration - waitedTime));
        }

        ResetReplicas();
        Thread.sleep(1000);
        if(false){

            try {
                System.out.println( getCurrentTimeStamp() +"Press enter to start next test");
                System.in.read();
            } catch (IOException e) {
                e.printStackTrace();
            }
        }
        return duration;
    }

    //Erster Test
    private static long TestNoWrapper() throws InterruptedException {

      /*TEST ABFOLGE:
        2 Random bid sequenzen (fur die beiden systeme) für alle tests gleich (aus vergleichs gründen)
        System 1:
        registriert 2 user (Hans, Peter)
        wartet
        startet auktion
        bid sequenz 1
        wartet bis auktionszeit rum ist
        stoppt auktion
        bestimmt gewinner
        System 2:
        registriert 2 user + 1 user der dem ersten system gleicht (Eve, Bob, Peter)
        wartet auf auktionsstart
        bid sequenz 2
        wartet auf auktionsende
        plaziert bid
        bestimmt gewinner
        -------------------------
        Bids:
        Sys1:user 1 -> user 2 -> user 1 -> user 2
        Sys2:user 1 -> user 2 -> user 3 -> user 1 -> user 2 -> user 3
        */
        long waitTime = 0;
        long timer = 0;
        long[] bidTimer = new long[sysBids.length];
        if(sysNr == 0){
            JRef<@Strong T1Auctioneer> auct = sys.replicate("auctioneer", new T1Auctioneer(), JConsistencyLevels.WEAK);
            Client c1 = auct.invoke("RegisterUser", "Hans");
            Client c2 = auct.invoke("RegisterUser", "Peter");

            Thread.sleep(1000);

            auct.invoke("StartAuction");

            long startTime = System.currentTimeMillis();

            Client c;
            for(int i = 0; i < sysBids.length; i++){
                if(i % 2 == 0)c = c1;
                else c = c2;
                timer = System.currentTimeMillis();
                auct.ref().PlaceBid(c.getClientID(), sysBids[i]);
                bidTimer[i] = System.currentTimeMillis() - timer;
                waitTime += 50;
                Thread.sleep(50);
            }
            /*
            System.out.println( getCurrentTimeStamp() +"Barrier");
            sys.barrier("barrier_1");
             */
            while(System.currentTimeMillis() - startTime < 2000){
                Thread.sleep(100);
                waitTime += 100;
            }



            System.out.println( getCurrentTimeStamp() +"The winner is: " + auct.invoke("CloseAuction"));


            auct.invoke("ShowBids");


        }
        else if(sysNr == 1){
            JRef<@Strong T1Auctioneer> auct = sys.lookup("auctioneer", (Class<@Weak T1Auctioneer>) T1Auctioneer.class, JConsistencyLevels.WEAK);

            Client c1 = auct.invoke("RegisterUser", "Eve");
            Client c2 = auct.invoke("RegisterUser", "Bob");
            Client c3 = auct.invoke("RegisterUser", "Peter");
            int counter = 0;
            boolean b = auct.ref().auctionRunning;
            while(b == false){
                counter++;
                waitTime += 50;
                Thread.sleep(50);
                if(counter>= 50)break;
            }
            if(counter< 10){
                long startTime = System.currentTimeMillis();

                Client c;
                for(int i = 0; i < sysBids.length; i++){
                    if(i % 2 == 0)c = c1;
                    else c = c2;
                    timer = System.currentTimeMillis();
                    auct.ref().PlaceBid(c.getClientID(), sysBids[i]);
                    bidTimer[i] = System.currentTimeMillis() - timer;
                    waitTime += 50;
                    Thread.sleep(50);
                }

                while(System.currentTimeMillis() - startTime < 2000){
                    Thread.sleep(100);
                    waitTime += 100;
                }

                boolean auctionStopped = false;
                while(System.currentTimeMillis() - startTime < 40000){
                    if(auct.ref().auctionRunning){
                        System.out.println( getCurrentTimeStamp() +"Waiting for auction to stop!");
                        Thread.sleep(100);
                        waitTime += 100;
                    }
                    else{
                        auctionStopped = true;
                    }
                }
                if(!auctionStopped){
                    System.out.println( getCurrentTimeStamp() +"Timeout while waiting for auction to stop!");
                }
            }
            else{
                System.out.println( getCurrentTimeStamp() +"Timeout while waiting for auction to stop!");
            }



            auct.invoke("ShowBids");

        }
        float time = 0;
        for(int i = 0; i < bidTimer.length; i++){
            time += bidTimer[i];
        }
        time = time / bidTimer.length;
        System.out.println( getCurrentTimeStamp() +"The Average bid time was: " + time);
        return waitTime;

    }

    //Zweiter Test
    public static long TestStrongWrapper()throws InterruptedException{
        //Testing:
        //Bid on weak auctioneer
        //Start and Closing of the Auction are done through a Strong wrapper
        long waitTime = 0;
        long timer = 0;
        long[] bidTimer = new long[sysBids.length];

        if(sysNr == 0){
            JRef<@Weak T2WeakSubAuct> auct = sys.replicate("auct", new T2WeakSubAuct(), JConsistencyLevels.WEAK);
            JRef<@Strong T2StrongAuctSys> wrapper = sys.replicate("auctionWrapper", new T2StrongAuctSys(auct), JConsistencyLevels.STRONG);
            sys.barrier("barrier_2_1");
            Client c1 = wrapper.invoke("RegisterUser", "Hans");
            Client c2 = wrapper.invoke("RegisterUser", "Peter");

            Thread.sleep(1000);

            wrapper.invoke("StartAuction");

            long startTime = System.currentTimeMillis();

            Client c;
            for(int i = 0; i < sysBids.length; i++){
                if(i % 2 == 0)c = c1;
                else c = c2;
                timer = System.currentTimeMillis();
                auct.ref().PlaceBid(c.getClientID(), sysBids[i]);
                bidTimer[i] = System.currentTimeMillis() - timer;
                System.out.println("Bid took " + bidTimer[i]);
                waitTime += 50;
                Thread.sleep(50);
            }

            while(System.currentTimeMillis() - startTime < 2000){
                Thread.sleep(100);
                waitTime += 100;
            }
            auct.syncAll();
            System.out.println( getCurrentTimeStamp() +"The winner is: " + wrapper.invoke("CloseAuction"));


            auct.invoke("ShowBids");
            sys.barrier("barrier_2");
        }
        else if(sysNr == 1){
            JRef<@Weak T2WeakSubAuct> auct = sys.lookup("auct", (Class<@Weak T2WeakSubAuct>) T2WeakSubAuct.class, JConsistencyLevels.WEAK);
            JRef<@Strong T2StrongAuctSys> wrapper = sys.lookup("auctionWrapper", (Class<@Strong T2StrongAuctSys>) T2StrongAuctSys.class, JConsistencyLevels.STRONG);
            sys.barrier("barrier_2_1");
            Client c1 = wrapper.invoke("RegisterUser", "Eve");
            Client c2 = wrapper.invoke("RegisterUser", "Bob");
            Client c3 = wrapper.invoke("RegisterUser", "Peter");
            boolean b = auct.ref().auctionRunning;
            int counter = 0;
            while(b == false && counter < 16){
                waitTime += 50;
                Thread.sleep(50);
                if(counter % 4 == 0)System.out.println(getCurrentTimeStamp() + " waiting for auction to Start");
                b = auct.ref().auctionRunning;
                counter++;
                auct.syncAll();//Ohne sync klappt nichts
            }


            long startTime = System.currentTimeMillis();

            Client c;
            for(int i = 0; i < sysBids.length; i++){
                if(i % 2 == 0)c = c1;
                else c = c2;
                timer = System.currentTimeMillis();
                auct.ref().PlaceBid(c.getClientID(), sysBids[i]);
                bidTimer[i] = System.currentTimeMillis() - timer;
                waitTime += 50;
                Thread.sleep(50);
            }

            while(System.currentTimeMillis() - startTime < 2000){
                Thread.sleep(100);
                waitTime += 100;
            }

            counter = 0;
            b = auct.ref().auctionRunning;
            while(b && counter < 10){
                    System.out.println( getCurrentTimeStamp() +"Waiting for auction to stop!");
                    b = auct.ref().auctionRunning;
                    Thread.sleep(100);
                    waitTime += 100;
                    auct.syncAll();
                    counter++;
            }
            if(auct.ref().auctionRunning){
                System.out.println( getCurrentTimeStamp() +"Timeout while waiting for auction to stop!");
            }

            auct.invoke("ShowBids");
            sys.barrier("barrier_2");
        }

        float time = 0;
        for(int i = 0; i < bidTimer.length; i++){
            time += bidTimer[i];
        }
        time = time / bidTimer.length;
        System.out.println( getCurrentTimeStamp() +"The Average bid time was: " + time);

        return waitTime;


    }

    //Dritter Test
    private static long TestWeakToStrong()throws  InterruptedException{
        //Testing:
        //Bid on weak wrapper
        //Start and Closing of the Auction are done through a Strong sub system
        long waitTime = 0;
        long timer = 0;
        long[] bidTimer = new long[sysBids.length];

        if(sysNr == 0){
            JRef<@Strong T3SubSystemStrong> subSys = sys.replicate("auctionWrapper2", new T3SubSystemStrong(), JConsistencyLevels.STRONG);
            JRef<@Weak T3WeakBidSystem> weakWrap = sys.replicate("auct", new T3WeakBidSystem(subSys), JConsistencyLevels.WEAK);
            sys.barrier("barrier_3_1");
            Client c1 = weakWrap.invoke("RegisterUser", "Hans");
            Client c2 = weakWrap.invoke("RegisterUser", "Peter");

            Thread.sleep(1000);

            weakWrap.invoke("StartAuction");

            long startTime = System.currentTimeMillis();

            Client c;
            for(int i = 0; i < sysBids.length; i++){
                if(i % 2 == 0)c = c1;
                else c = c2;

                timer = System.currentTimeMillis();
                weakWrap.ref().AddBid(c.getClientID(), sysBids[i]);
                bidTimer[i] = System.currentTimeMillis() - timer;

                waitTime += 50;
                Thread.sleep(50);
            }

            while(System.currentTimeMillis() - startTime < 2000){
                Thread.sleep(100);
                waitTime += 100;
            }
            subSys.ref().StopAuction();

            sys.barrier("barrier_3");
            weakWrap.syncAll();
            subSys.syncAll();
            sys.barrier("barrier_3.5");//Synced nicht
            weakWrap.ref().ShowBids();
            System.out.println( getCurrentTimeStamp() +"The winner is: " + weakWrap.ref().CloseAuction());
            sys.barrier("barrier_3_end");
        }
        else if(sysNr == 1){
            JRef<@Strong T3SubSystemStrong> subSys = sys.lookup("auctionWrapper2", (Class<@Strong T3SubSystemStrong>) T3SubSystemStrong.class, JConsistencyLevels.STRONG);
            JRef<@Weak T3WeakBidSystem> weakWrap = sys.lookup("auct", (Class<@Weak T3WeakBidSystem>) T3WeakBidSystem.class, JConsistencyLevels.WEAK);
            sys.barrier("barrier_3_1");
            Client c1 = weakWrap.invoke("RegisterUser", "Eve");
            Client c2 = weakWrap.invoke("RegisterUser", "Bob");
            Client c3 = weakWrap.invoke("RegisterUser", "Peter");

            boolean b = subSys.ref().auctionRunning;
            int counter = 0;
            while(b == false && counter < 10){
                waitTime += 50;
                Thread.sleep(50);
                if(counter % 4 == 0)System.out.println(getCurrentTimeStamp() + " waiting for auction to Start");
                b = subSys.ref().auctionRunning;
                subSys.syncAll();
                counter++;
            }

            long startTime = System.currentTimeMillis();

            Client c;
            for(int i = 0; i < sysBids.length; i++){
                if(i % 2 == 0)c = c1;
                else c = c2;
                timer = System.currentTimeMillis();
                weakWrap.ref().AddBid(c.getClientID(), sysBids[i]);
                bidTimer[i] = System.currentTimeMillis() - timer;
                waitTime += 50;
                Thread.sleep(50);
            }

            while(System.currentTimeMillis() - startTime < 2000){
                Thread.sleep(100);
                waitTime += 100;
            }

            counter = 0;
            b = subSys.ref().auctionRunning;
            while(b && counter < 10){
                System.out.println( getCurrentTimeStamp() +"Waiting for auction to stop!");
                Thread.sleep(100);
                waitTime += 100;
                //subSys.syncAll();
                //weakWrap.syncAll();
                counter++;
            }
            if(subSys.ref().auctionRunning){
                System.out.println( getCurrentTimeStamp() +"Timeout while waiting for auction to stop!");
            }
            sys.barrier("barrier_3");
            weakWrap.syncAll();
            subSys.syncAll();
            sys.barrier("barrier_3.5");
            weakWrap.invoke("ShowBids");
            sys.barrier("barrier_3_end");
        }

        float time = 0;
        for(int i = 0; i < bidTimer.length; i++){
            time += bidTimer[i];
        }
        time = time / bidTimer.length;
        System.out.println( getCurrentTimeStamp() +"The Average bid time was: " + time);

        return waitTime;

    }

    //Vierter Test (Nicht für Verteilte Systeme Geeignet & Veraltet)
    public static long TestCreateBidSubSys()throws InterruptedException{

        long waitTime = 0;
        long timer = 0;
        long[] bidTimer = new long[sysBids.length];

        if(sysNr == 0){
            JRef<@Strong T4StrongSys> strongSys = sys.replicate("strongSys", new T4StrongSys(), JConsistencyLevels.STRONG);

            strongSys.ref().SetSys(sys, sysNr);

            Client c1 = strongSys.invoke("RegisterUser", "Hans");
            Client c2 = strongSys.invoke("RegisterUser", "Peter");


            Thread.sleep(1000);
            boolean b = strongSys.ref().StartAuction();
            int count = 0;
            while(!b){
                waitTime += 50;
                count++;
                Thread.sleep(50);
                b = strongSys.ref().StartAuction();
                System.out.println( getCurrentTimeStamp() + " trying to start Auction");
                if(count >= 20)break;
            }
            if(strongSys.ref().AuctionRunning()){
                JRef<@Weak T4BidSystem> bidsys = strongSys.ref().GetBidSys(sysNr);
                strongSys.ref().StartAuction();
                long startTime = System.currentTimeMillis();

                Client c;
                for(int i = 0; i < sysBids.length - 2; i++){
                    if(i % 2 == 0)c = c1;
                    else c = c2;

                    timer = System.currentTimeMillis();
                    bidsys.ref().Bid(new Bid(c.getClientID(), sysBids[i]));
                    bidTimer[i] = System.currentTimeMillis() - timer;



                    waitTime += 50;
                    Thread.sleep(50);
                }

                while(System.currentTimeMillis() - startTime < 2000){
                    Thread.sleep(100);
                    waitTime += 100;
                }



                System.out.println( getCurrentTimeStamp() +"The winner is: " + strongSys.ref().CloseAuction());


                strongSys.ref().ShowBids(sysNr);
            }



        }
        else if(sysNr == 1){
            JRef<@Strong T4StrongSys> strongSys = sys.lookup("strongSys", T4StrongSys.class, JConsistencyLevels.STRONG);

            strongSys.ref().SetSys(sys, sysNr);

            Client c1 = strongSys.invoke("RegisterUser", "Eve");
            Client c2 = strongSys.invoke("RegisterUser", "Bob");
            Client c3 = strongSys.invoke("RegisterUser", "Peter");


            int count = 0;

            boolean b = strongSys.ref().AuctionRunning();
            while(!b){
                waitTime += 50;
                count++;
                Thread.sleep(50);
                b = strongSys.ref().AuctionRunning();
                System.out.println( getCurrentTimeStamp() + " waiting for subsys");
                if(count >= 20)break;
            }
            if(strongSys.ref().AuctionRunning()){
                JRef<@Weak T4BidSystem> bidsys = strongSys.ref().GetBidSys(sysNr);
                long startTime = System.currentTimeMillis();

                Client c;
                for(int i = 0; i < sysBids.length; i++){
                    if(i % 2 == 0)c = c1;
                    else c = c2;
                    timer = System.currentTimeMillis();
                    bidsys.ref().Bid(new Bid(c.getClientID(), sysBids[i]));
                    bidTimer[i] = System.currentTimeMillis() - timer;
                    waitTime += 50;
                    Thread.sleep(50);
                }

                while(System.currentTimeMillis() - startTime < 2000){
                    Thread.sleep(100);
                    waitTime += 100;
                }

                boolean auctionStopped = false;
                while(System.currentTimeMillis() - startTime < 40000){
                    if(bidsys.ref().GetEnabled()){
                        System.out.println( getCurrentTimeStamp() +"Waiting for auction to stop!");
                        Thread.sleep(100);
                        waitTime += 100;
                    }
                    else{
                        auctionStopped = true;
                    }
                }
                if(!auctionStopped){
                    System.out.println( getCurrentTimeStamp() +"Timeout while waiting for auction to stop!");
                }

                strongSys.ref().ShowBids(sysNr);
            }
            else {
                System.out.println( getCurrentTimeStamp() + " Timeout waiting for Bid Sub sys to be created");
            }


        }

        float time = 0;
        for(int i = 0; i < bidTimer.length; i++){
            time += bidTimer[i];
        }
        time = time / bidTimer.length;
        System.out.println( getCurrentTimeStamp() +"The Average bid time was: " + time);

        return waitTime;

    }

    //Lässt die Tests einmal durchlaufen ohne Timer
    public static void Warmup()throws Exception{
        RunTest(1, false);
        RunTest(2, false);
        RunTest(3, false);
        //RunTest(4, false);
    }

}
