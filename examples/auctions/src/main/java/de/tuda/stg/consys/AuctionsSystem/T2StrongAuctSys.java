package de.tuda.stg.consys.AuctionsSystem;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.JRef;

import java.io.Serializable;

public class T2StrongAuctSys implements Serializable {


    public JRef<@Weak T2WeakSubAuct> auctioneer;

    public T2StrongAuctSys(JRef<@Weak T2WeakSubAuct> a) {
        this.auctioneer = a;
    }

    boolean StartAuction(){
        return auctioneer.invoke("StartAuction");
    }

    int CloseAuction(){
        return auctioneer.invoke("CloseAuction");
    }

    boolean StopAuction(){
        return auctioneer.invoke("StopAuction");
    }

    public Client RegisterUser(String name){
        return auctioneer.invoke("RegisterUser", name);
    }



}
