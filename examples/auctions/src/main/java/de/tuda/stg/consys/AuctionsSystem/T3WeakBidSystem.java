package de.tuda.stg.consys.AuctionsSystem;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.JRef;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

public class T3WeakBidSystem implements Serializable {
    public JRef<@Strong T3SubSystemStrong> sys;
    List<Bid> bids;

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
            System.out.println("Bid: " + bid.clientID + " - " + bid.bid);
        }
    }

    boolean AddBid(int clientId, int bid){
        System.out.println("Placing Bid");
        if(sys.invoke("GetAuctionStatus")){
            System.out.println("Failed. Auction not running.");
            return false;
        }
        if(!sys.<Boolean>invoke("IsUserRegistered", clientId)){
            return false;
        }
        System.out.println("Bid placed");
        bids.add(new Bid(clientId, bid));
        return true;
    }

    /*
        If the auction has ended this method returns the winner and clears all bids
        Returns the winner id - or 0 if no winner is available
    */
    int CloseAuction(){
        if(!sys.<Boolean>invoke("GetAuctionStatus")){
            int winner = 0;
            int highestBid = 0;
            for (Bid bid : bids) {
                if(bid.bid > highestBid)winner = bid.clientID;
            }
            bids = new ArrayList<>();
            return winner;
        }
        else{
            return 0;
        }

    }



}
