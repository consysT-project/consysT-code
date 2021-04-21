package de.tuda.stg.consys.examples.auctions;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

public class T5BidSystemOnMain implements Serializable {

    boolean enabled;
    List<Bid> bids;
    List<Client> registeredUsers;

    public T5BidSystemOnMain(List<Client> registeredUsers){
        this.registeredUsers = registeredUsers;
        bids = new ArrayList<>();
        enabled = true;
    }

    public boolean Bid(Bid b){
        if(enabled && HasUserID(b.clientID)){
            bids.add(b);
            System.out.println("Bid: " + b.bid + " by: " + b.clientID + " accepted!");
            return true;
        }
        System.out.println("Bid: " + b.bid + " by: " + b.clientID + " rejected!");
        return false;
    }

    private boolean HasUserID(int id){
        for(Client c: registeredUsers){
           if(c.getClientID() == id)return true;
        }
        return false;
    }

    public boolean StopAuction(){
        if(enabled){
            enabled = false;
            return true;
        }
        return false;
    }

    public boolean GetEnabled(){
        return enabled;
    }

    public List<Bid> GetBids(){
        return bids;
    }

}
