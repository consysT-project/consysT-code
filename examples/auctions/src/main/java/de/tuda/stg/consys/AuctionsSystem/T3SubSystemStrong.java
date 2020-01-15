package de.tuda.stg.consys.AuctionsSystem;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

public class T3SubSystemStrong implements Serializable {

    boolean auctionRunning;
    List<Client> registeredUsers;

    public T3SubSystemStrong(){
        this.auctionRunning = false;
        registeredUsers = new ArrayList<>();
    }

    /*
    Starts the Auction process, so that Bids can be places as long as its running.
    Returns true if auction was started successfully,
    Returns false if the auction was already running.
     */
    boolean StartAuction(){
        if(auctionRunning)return false;
        System.out.println("Auction started!");
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


    public Client RegisterUser(String name){
        for(Client c : registeredUsers){
            if(c.getName() == name)return null;
        }
        Client client = new Client(name, registeredUsers.size() + 1);
        registeredUsers.add(client);
        System.out.println("Created " + client.getName() + " with ID: " + client.getClientID());
        return client;
    }

    boolean IsUserRegistered(int clientID){
        for(Client c : registeredUsers){
            if(c.getClientID() == clientID){
                System.out.println(("Client " + clientID + " found"));
                return true;
            }
        }
        System.out.println(("Client " + clientID + " is not registered"));
        return false;
    }

    boolean GetAuctionStatus(){
        return auctionRunning;
    }




}
