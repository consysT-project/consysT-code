package de.tuda.stg.consys.examples.auctions;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class T3WeakBidSystem implements Serializable {
    public JRef<@Strong T3SubSystemStrong> sys;
    List<Bid> bids;

    /*
    Testklasse 3:
    Umgekehrter Testfall zu 2.
    Die Wrapper klasse ist Weak. Auf dieser werden gebote ausgeführt. STart und Stopp der Auction werden an die Strong SUbklasse weitergeleitet
     */
    public T3WeakBidSystem(JRef<@Strong T3SubSystemStrong> s){
        sys = s;
        bids = new ArrayList<>();
    }

    boolean StartAuction(){
        return sys.invoke("StartAuction");
    }

    boolean StopAuction(){
        return sys.invoke("StopAuction");
    }


    public Client RegisterUser(String name){
        return sys.invoke("RegisterUser", name);
    }


    void ShowBids(){
        for (Bid bid : bids) {
            System.out.println(getCurrentTimeStamp() +" Bid: " + bid.clientID + " - " + bid.bid);
        }
    }
    public static String getCurrentTimeStamp() {
        SimpleDateFormat sdfDate = new SimpleDateFormat("HH:mm:ss");//dd/MM/yyyy
        Date now = new Date();
        String strDate = sdfDate.format(now);
        return strDate;
    }

    boolean AddBid(int clientId, int bid){
        boolean b = sys.ref().GetAuctionStatus();
        if(!b){
            System.out.println(getCurrentTimeStamp() +" Failed to place bid. Auction not running.");
            return false;
        }
        boolean c = sys.ref().IsUserRegistered(clientId);
        if(!c){
            System.out.println(getCurrentTimeStamp() +" Failed to place bid. User not found.");
            return false;
        }
        System.out.println(getCurrentTimeStamp() +" Bid: " + bid + " by: " + clientId + " accepted!");
        bids.add(new Bid(clientId, bid));
        return true;
    }

    /*
        If the auction has ended this method returns the winner and clears all bids
        Returns the winner id - or 0 if no winner is available
    */
    int CloseAuction(){
        System.out.println(getCurrentTimeStamp() +" Determining the winner...");
        boolean b = sys.ref().GetAuctionStatus();
        if(!b){
            int winner = 0;
            int highestBid = 0;
            for (Bid bid : bids) {
                if(bid.bid > highestBid){
                    winner = bid.clientID;
                    highestBid = bid.bid;
                }
                //System.out.println("Bid: " + bid.bid +  " by " + bid.clientID + " - current Highest Bid: " + highestBid + " by " + winner);
            }
            bids = new ArrayList<>();
            return winner;
        }
        else{
            return 0;
        }

    }



}
