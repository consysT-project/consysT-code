package de.tuda.stg.consys.AuctionsSystem;

import java.io.Serializable;

public class Bid implements Serializable {
    int itemID;
    int clientID;
    int bid;

    public Bid(int itemID, int clientID, int bid) {
        this.itemID = itemID;
        this.clientID = clientID;
        this.bid = bid;
    }

    public Bid(int clientID, int bid) {
        this.clientID = clientID;
        this.bid = bid;
    }
}
