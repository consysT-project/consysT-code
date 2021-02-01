package de.tuda.stg.consys.examples.auctions;

import java.io.Serializable;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;

public class T1Auctioneer implements Serializable {
    boolean auctionRunning;
    List<Bid> bids;
    List<Client> registeredUsers;
    int winner = -1;

    //Erste Testklasse
    //Keinerlei Konsistenz features
    public T1Auctioneer(){
        this.auctionRunning = false;
        bids = new ArrayList<>();
        registeredUsers = new ArrayList<>();
    }

    /*
    Starts the Auction process, so that Bids can be placed as long as its running.
    Returns true if auction was started successfully,
    Returns false if the auction was already running.
     */
    boolean StartAuction(){
        if(auctionRunning)return false;
        System.out.println(getCurrentTimeStamp() + " Auction started!");
        bids = new ArrayList<>();
        auctionRunning = true;
        return true;
    }
    /*
    Closes the Auction and finds the winner.
    Returns the winner id - or 0 if no winner is available
     */
    int CloseAuction(){
        auctionRunning = false;
        winner = 0;
        int highestBid = 0;
        for (Bid bid : bids) {
            if(bid.bid > highestBid){
                winner = bid.clientID;
                highestBid = bid.bid;
            }
        }
        return winner;
    }

    public int GetWinner(){
        return winner;
    }
    void ShowBids(){
        for (Bid bid : bids) {
            System.out.println(getCurrentTimeStamp() + " Bid: " + bid.clientID + " - " + bid.bid);
        }
    }

    /*
    Plaziert ein Gebot
     */
    boolean PlaceBid(int clientId, int bid){
        if(!auctionRunning){
            System.out.println(getCurrentTimeStamp() + " Failed to place bid. Auction not running.");
            return false;
        }
        if(!IsUserRegistered(clientId)){
            return false;
        }
        System.out.println( getCurrentTimeStamp() +"Bid: " + bid + " by: " + clientId + " placed!");
        bids.add(new Bid(clientId, bid));
        return true;
    }

    /*
    Checkt ob der gegebene Nutzer registriert ist
     */
    boolean IsUserRegistered(int clientID){
        for(Client c : registeredUsers){
            if(c.getClientID() == clientID){
                //System.out.println((getCurrentTimeStamp() + " Client " + clientID + " found"));
                return true;
            }
        }

        System.out.println((getCurrentTimeStamp() +  " Client " + clientID + " is not registered"));
        return false;
    }

    /*
    Registriert einen Nutzer, so das dieser mit Bieten kann
     */
    public Client RegisterUser(String name){
        for(Client c : registeredUsers){
            if(c.getName() == name)return null;
        }
        Client client = new Client(name, registeredUsers.size() + 1);
        registeredUsers.add(client);
        System.out.println(getCurrentTimeStamp() + " Created " + client.getName() + " with ID: " + client.getClientID());
        return client;
    }

    /*
    Gibt einen String mit der Aktuellen Uhrzeit im Format HH:MM::SS zurück
     */
    public static String getCurrentTimeStamp() {
        SimpleDateFormat sdfDate = new SimpleDateFormat("HH:mm:ss");//dd/MM/yyyy
        Date now = new Date();
        String strDate = sdfDate.format(now);
        return strDate;
    }

}
