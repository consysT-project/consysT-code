package de.tuda.stg.consys.examples.auctions;

import java.io.Serializable;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class T4BidSystem implements Serializable {

    boolean enabled;
    List<Bid> bids;
    List<Client> registeredUsers;

    public T4BidSystem(List<Client> registeredUsers){
        this.registeredUsers = registeredUsers;
        bids = new ArrayList<>();
        enabled = true;
    }

    public boolean Bid(Bid b){
        if(enabled && HasUserID(b.clientID)){
            bids.add(b);
            System.out.println( getCurrentTimeStamp() +" Bid: " + b.bid + " by: " + b.clientID + " accepted!");
            return true;
        }
        System.out.println( getCurrentTimeStamp() +" Bid: " + b.bid + " by: " + b.clientID + " rejected!");
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
    public static String getCurrentTimeStamp() {
        SimpleDateFormat sdfDate = new SimpleDateFormat("HH:mm:ss");//dd/MM/yyyy
        Date now = new Date();
        String strDate = sdfDate.format(now);
        return strDate;
    }
}
