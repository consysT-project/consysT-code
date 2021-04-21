package de.tuda.stg.consys.examples.auctions;

import java.io.Serializable;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class T2WeakSubAuct implements Serializable {

    boolean auctionRunning;
    List<Client> registeredUsers;
    List<Bid> bids;
    /*
       Zweite Testklasse:
       Gebote werden auf Weak subklasse ausgeführt,
       der rest auf der Strong Wrapper Klasse
        */
    public T2WeakSubAuct(){
        auctionRunning = false;
        bids = new ArrayList<>();
        registeredUsers = new ArrayList<>();
    }

    /*
    Starts the Auction process, so that Bids can be places as long as its running.
    Returns true if auction was started successfully,
    Returns false if the auction was already running.
     */
    boolean StartAuction(){
        if(auctionRunning){
            System.out.println( getCurrentTimeStamp() +"Auction already running");
            return false;
        }
        System.out.println( getCurrentTimeStamp() +"Auction started!");
        bids = new ArrayList<>();
        auctionRunning = true;
        return true;
    }

    boolean StopAuction(){
        if(!auctionRunning){
            System.out.println( getCurrentTimeStamp() +"No Auction is aktive");
            return false;
        }
        auctionRunning = false;
        System.out.println( getCurrentTimeStamp() +"Auction stopped!");
        return true;
    }
    /*
    Closes the Auction and finds the winner.
    Returns the winner id - or 0 if no winner is available
     */
    int CloseAuction(){
        int winner = 0;
        int highestBid = 0;
        if(!auctionRunning){
            System.out.println(getCurrentTimeStamp() + " Failed to stop auction. Auction was not running.");
        }else{
            auctionRunning = false;
            System.out.println( getCurrentTimeStamp() +" Auction Closed!");

            for (Bid bid : bids) {
                if(bid.bid > highestBid){
                    winner = bid.clientID;
                    highestBid = bid.bid;
                }
            }
        }

        return winner;
    }

    void ShowBids(){
        for (Bid bid : bids) {
            System.out.println( getCurrentTimeStamp() +"Bid: " + bid.clientID + " - " + bid.bid);
        }
    }

    boolean PlaceBid(int clientId, int bid){
        if(!auctionRunning){
            System.out.println( getCurrentTimeStamp() +" Failed to place bid. Auction not running.");
            return false;
        }
        if(!IsUserRegistered(clientId)){
            System.out.println( getCurrentTimeStamp() +" Failed to place bid. Unknown user.");
            return false;
        }
        System.out.println( getCurrentTimeStamp() +" Bid: " + bid + " by: " + clientId + " accepted!");
        bids.add(new Bid(clientId, bid));
        return true;
    }

    boolean IsUserRegistered(int clientID){
        for(Client c : registeredUsers){
            if(c.getClientID() == clientID){
                //System.out.println( getCurrentTimeStamp() +("Client " + clientID + " found"));
                return true;
            }
        }
        //System.out.println( getCurrentTimeStamp() +("Client " + clientID + " is not registered"));
        return false;
    }

    public Client RegisterUser(String name){
        for(Client c : registeredUsers){
            if(c.getName() == name)return null;
        }
        Client client = new Client(name, registeredUsers.size() + 1);
        registeredUsers.add(client);
        System.out.println( getCurrentTimeStamp() +"Created " + client.getName() + " with ID: " + client.getClientID());
        return client;
    }
    public static String getCurrentTimeStamp() {
        SimpleDateFormat sdfDate = new SimpleDateFormat("HH:mm:ss");//dd/MM/yyyy
        Date now = new Date();
        String strDate = sdfDate.format(now);
        return strDate;
    }

}
