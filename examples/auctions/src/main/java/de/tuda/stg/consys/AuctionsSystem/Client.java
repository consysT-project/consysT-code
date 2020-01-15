package de.tuda.stg.consys.AuctionsSystem;

import java.io.Serializable;

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
