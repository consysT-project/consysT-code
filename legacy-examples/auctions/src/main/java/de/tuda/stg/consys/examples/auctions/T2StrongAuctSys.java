package de.tuda.stg.consys.examples.auctions;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;
import java.text.SimpleDateFormat;
import java.util.Date;

public class T2StrongAuctSys implements Serializable {


    public JRef<@Weak T2WeakSubAuct> auctioneer;
    /*
    Zweite Testklasse:
    Gebote werden auf Weak subklasse ausgeführt,
    der rest auf der Strong Wrapper Klasse
     */
    public T2StrongAuctSys(JRef<@Weak T2WeakSubAuct> a) {
        this.auctioneer = a;
    }

    boolean StartAuction(){
        return auctioneer.invoke("StartAuction");
    }

    int CloseAuction(){
        auctioneer.syncAll();
        return auctioneer.invoke("CloseAuction");

    }

    boolean StopAuction(){
        return auctioneer.invoke("StopAuction");
    }

    public Client RegisterUser(String name){
        return auctioneer.invoke("RegisterUser", name);
    }


    public static String getCurrentTimeStamp() {
        SimpleDateFormat sdfDate = new SimpleDateFormat("HH:mm:ss");//dd/MM/yyyy
        Date now = new Date();
        String strDate = sdfDate.format(now);
        return strDate;
    }
}
