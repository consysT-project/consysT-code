package de.tuda.stg.consys.AuctionsSystem;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

public class T2WeakSubAuct implements Serializable {

    boolean auctionRunning;
    List<Client> registeredUsers;
    List<Bid> bids;

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
            System.out.println("Auction already running");
            return false;
        }
        System.out.println("Auction started!");
        bids = new ArrayList<>();
        auctionRunning = true;
        return true;
    }

    boolean StopAuction(){
        if(!auctionRunning){
            System.out.println("No Auction is aktive");
            return false;
        }
        auctionRunning = false;
        System.out.println("Auction stopped!");
        return true;
    }
    /*
    Closes the Auction and finds the winner.
    Returns the winner id - or 0 if no winner is available
     */
    int CloseAuction(){
        if(auctionRunning){
            System.out.println("Auction is still running!");
            return 0;
        }
        System.out.println("Auction Closed!");
        int winner = 0;
        int highestBid = 0;
        for (Bid bid : bids) {
            if(bid.bid > highestBid)winner = bid.clientID;
        }
        return winner;
    }

    void ShowBids(){
        for (Bid bid : bids) {
            System.out.println("Bid: " + bid.clientID + " - " + bid.bid);
        }
    }

    boolean PlaceBid(int clientId, int bid){
        System.out.print("Placing Bid. ");
        if(!auctionRunning){
            System.out.println("Failed. Auction not running.");
            return false;
        }
        if(!IsUserRegistered(clientId)){
            System.out.println("Failed. Unknown user.");
            return false;
        }
        System.out.println("Bid: " + bid + " placed");
        bids.add(new Bid(clientId, bid));
        return true;
    }

    boolean IsUserRegistered(int clientID){
        for(Client c : registeredUsers){
            if(c.getClientID() == clientID){
                //System.out.println(("Client " + clientID + " found"));
                return true;
            }
        }
        //System.out.println(("Client " + clientID + " is not registered"));
        return false;
    }

    public Client RegisterUser(String name){
        for(Client c : registeredUsers){
            if(c.getName() == name)return null;
        }
        Client client = new Client(name, registeredUsers.size() + 1);
        registeredUsers.add(client);
        System.out.println("Created " + client.getName() + " with ID: " + client.getClientID());
        return client;
    }


}
