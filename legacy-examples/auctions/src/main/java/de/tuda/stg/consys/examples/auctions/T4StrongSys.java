package de.tuda.stg.consys.examples.auctions;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.akka.JAkkaReplicaSystem;

import java.io.Serializable;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class T4StrongSys implements Serializable {
    //Strongly consistent System that creates the Bidding system for an Auction
    //Currently only users that have been created before an auction can participate

    JRef<@Weak T4BidSystem> bidSys1;
    JRef<@Weak T4BidSystem> bidSys2;
    List<Client> registeredUsers;
    boolean rdy, oneSet, twoSet;
    JAkkaReplicaSystem sys0;
    JAkkaReplicaSystem sys1;
    //JReplicaSystem sys1;
    //JReplicaSystem sys2;


    public T4StrongSys(){
        registeredUsers = new ArrayList<>();
        rdy = false;
        oneSet = false;
        twoSet = false;

    }

    public Client RegisterUser(String name){
        for(Client c : registeredUsers){
            if(c.getName() == name)return null;
        }
        Client client = new Client(name, registeredUsers.size() + 1);
        registeredUsers.add(client);
        System.out.println( getCurrentTimeStamp() + " User " + client.getName() + " with id: " + client.getClientID() + " created.");
        return client;
    }

    public void StartAuction(JReplicaSystem sys1, JReplicaSystem sys2){
        //bidSys1 = Replicas.replicaSystem1.replicate("bidSys1", new T4BidSystem(registeredUsers), JConsistencyLevel.WEAK);
        //bidSys2 = Replicas.replicaSystem2.ref("bidSys1", (Class<@Weak T4BidSystem>) T4BidSystem.class, JConsistencyLevel.WEAK);
        bidSys1 = sys1.replicate("bidSys", new T4BidSystem(registeredUsers), JConsistencyLevels.WEAK);
        bidSys2 = sys2.lookup("bidSys", (Class<@Weak T4BidSystem>) T4BidSystem.class, JConsistencyLevels.WEAK);
    }

    public void SetSys(JAkkaReplicaSystem sys, int sysNr){
        System.out.println(getCurrentTimeStamp() + " Setting System");
        if(sysNr == 0){
            sys0 = sys;
            oneSet = true;

        }else if(sysNr == 1){
            sys1 = sys;
            twoSet = true;
        }
        System.out.println(getCurrentTimeStamp() + " Sys " + sysNr + " set.");
    }

    public boolean StartAuction(){
        System.out.println(getCurrentTimeStamp() + " Trying to start auction");
        if(oneSet && twoSet){
            bidSys1 = sys0.replicate("BidSys", new T4BidSystem(registeredUsers), JConsistencyLevels.WEAK);
            bidSys2 = sys1.lookup("BidSys", (Class<@Weak T4BidSystem>) T4BidSystem.class, JConsistencyLevels.WEAK);
            rdy = true;
            System.out.println(getCurrentTimeStamp() + " auction started.");
        }
        return rdy;
    }
    public boolean AuctionRunning(){
        return rdy;
    }

    public static String getCurrentTimeStamp() {
        SimpleDateFormat sdfDate = new SimpleDateFormat("HH:mm:ss");//dd/MM/yyyy
        Date now = new Date();
        String strDate = sdfDate.format(now);
        return strDate;
    }

    public boolean StopAuction(){
        boolean b = false;
        bidSys2.syncAll();//Sync needs to be done befor stopping the auction so all auctions get synced

        try{
            b = bidSys1.invoke("StopAuction");
        }
        catch (Exception e){
            System.out.println( getCurrentTimeStamp() + " Cant stop auction - No Auction running");
        }
        //bidSys1.sync();

        return b;
    }

    public JRef<@Weak T4BidSystem> GetBidSys(int nr){
        switch (nr){
            case 0:
                return bidSys1;
            case 1:
                return bidSys2;
                default:
                    System.out.println("No bidystem returned");
                    return null;
        }
    }

    public Client GetClient(int id){
        for (Client c : registeredUsers) {
            if(c.getClientID() == id)return c;
        }
        return null;
    }

    public int CloseAuction(){
        boolean b = bidSys1.invoke("GetEnabled");
        if(!b){
            return 0;
        }
        else{
            bidSys1.ref().StopAuction();
            int winner = 0;
            int highestBid = 0;
            List<Bid> bids = bidSys1.invoke("GetBids");
            for (Bid bid : bids) {
                System.out.println( getCurrentTimeStamp() + " " + bid.bid + " by " + bid.clientID);
                if(bid.bid > highestBid){
                    winner = bid.clientID;
                    highestBid = bid.bid;
                }
            }
            return winner;
        }

    }

    public void ShowBids(int nr){
        if(nr == 0){
            System.out.println( getCurrentTimeStamp() + " bid sys 1 - Bids:");
            List<Bid> bids = bidSys1.ref().GetBids();
            for (Bid bid : bids ) {
                System.out.println( getCurrentTimeStamp() +" Bid: " + bid.clientID + " - " + bid.bid);
            }
        }else if(nr == 1){
            System.out.println( getCurrentTimeStamp() +" bid sys 2 - Bids:");
            List<Bid> bids = bidSys2.ref().GetBids();
            for (Bid bid : bids) {
                System.out.println( getCurrentTimeStamp() +" Bid: " + bid.clientID + " - " + bid.bid);
            }
        }
    }

}
