package de.tuda.stg.consys.examples.auctions;

import java.io.Serializable;

//Klasse die ein Gebot repräsentiert
//Ein gebot hat die ID des Bieters und einen Wert
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
