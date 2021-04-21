package de.tuda.stg.consys.examples.auctions;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

public class T5StrongSys implements Serializable {
    //Strongly consistent System that creates the Bidding system for an Auction
    //Currently only users that have been created before an auction can participate

    JRef<@Weak T5BidSystemOnMain> bidSys1;
    JRef<@Weak T5BidSystemOnMain> bidsys2;
    List<Client> registeredUsers;


    public T5StrongSys(){
        registeredUsers = new ArrayList<>();
    }

    public Client RegisterUser(String name){
        for(Client c : registeredUsers){
            if(c.getName() == name)return null;
        }
        Client client = new Client(name, registeredUsers.size() + 1);
        registeredUsers.add(client);
        return client;
    }

    public void StartAuction(JRef<@Weak T5BidSystemOnMain> bidsys1, JRef<@Weak T5BidSystemOnMain> bidsys2){
        this.bidSys1 = bidsys1;
        this.bidsys2 = bidsys2;
    }


    private void CanStartAuction(){
        if(bidSys1 != null && bidsys2 != null){

        }
    }
    public boolean StopAuction(){
        boolean b = false;
        try{
            b = bidSys1.invoke("StopAuction");
        }
        catch (Exception e){
            System.out.println("Cant stop auction - No Auction running");
        }
        bidSys1.sync();
        return b;
    }

    public JRef<@Weak T5BidSystemOnMain> GetBidSys(int nr){
        switch (nr){
            case 1:
                return bidSys1;
            case 2:
                return bidsys2;

                default:
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
        if(bidSys1.invoke("GetEnabled")){
            return 0;
        }
        else{
            int winner = 0;
            int highestBid = 0;
            List<Bid> bids = bidSys1.invoke("GetBids");
            for (Bid bid : bids) {
                if(bid.bid > highestBid)winner = bid.clientID;
            }
            return winner;
        }

    }

}
