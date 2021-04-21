package de.tuda.stg.consys.examples.auctions;

import java.io.Serializable;

//Klasse die Einen User repräsentiert.
//Der User hat einen Namen und eine ID
public class Client implements Serializable {

    private int clientID;
    private String name;

    public Client(String name, int id) {
        this.name = name;
        this.clientID = id;
    }

    public int getClientID() {
        return clientID;
    }


    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }
}
