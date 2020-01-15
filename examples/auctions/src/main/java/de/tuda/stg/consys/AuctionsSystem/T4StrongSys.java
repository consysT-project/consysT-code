package de.tuda.stg.consys.AuctionsSystem;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.JConsistencyLevels;
import de.tuda.stg.consys.japi.JRef;
import de.tuda.stg.consys.japi.JReplicaSystem;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

public class T4StrongSys implements Serializable {
    //Strongly consistent System that creates the Bidding system for an Auction
    //Currently only users that have been created before an auction can participate

    JRef<@Weak T4BidSystem> bidSys1;
    JRef<@Weak T4BidSystem> bidSys2;
    List<Client> registeredUsers;
    //JReplicaSystem sys1;
    //JReplicaSystem sys2;


    public T4StrongSys(){
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

    public void StartAuction(JReplicaSystem sys1, JReplicaSystem sys2){
        double r = Math.random();
        System.out.println("R: " + r);
        //bidSys1 = Replicas.replicaSystem1.replicate("bidSys1", new T4BidSystem(registeredUsers), JConsistencyLevel.WEAK);
        //bidSys2 = Replicas.replicaSystem2.ref("bidSys1", (Class<@Weak T4BidSystem>) T4BidSystem.class, JConsistencyLevel.WEAK);
        bidSys1 = sys1.replicate(Double.toString(r), new T4BidSystem(registeredUsers), JConsistencyLevels.WEAK);
        bidSys2 = sys2.lookup(Double.toString(r), (Class<@Weak T4BidSystem>) T4BidSystem.class, JConsistencyLevels.WEAK);
    }

    public boolean StopAuction(){
        boolean b = false;
        bidSys2.syncAll();//Sync needs to be done befor stopping the auction so all auctions get synced

        try{
            b = bidSys1.invoke("StopAuction");
        }
        catch (Exception e){
            System.out.println("Cant stop auction - No Auction running");
        }
        //bidSys1.sync();

        return b;
    }

    public JRef<@Weak T4BidSystem> GetBidSys(int nr){
        switch (nr){
            case 1:
                return bidSys1;
            case 2:
                return bidSys2;

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
                System.out.println(bid.bid + " by " + bid.clientID);
                if(bid.bid > highestBid)winner = bid.clientID;
            }
            return winner;
        }

    }

}
