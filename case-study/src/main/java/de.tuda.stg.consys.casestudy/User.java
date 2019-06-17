package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.util.LinkedList;

public class User {

    public String userID;

    private String password;

    private boolean isLoggedIn;

    private LinkedList<JReplicaSystem> loggedInFrom;

    public String description;

    private double balance;

    private JRef<@Strong Cart> cart;

    User(String userID, String password, JReplicaSystem system){
        this.userID = userID; this.password = password;
        isLoggedIn = false; loggedInFrom = new LinkedList<JReplicaSystem>();
        balance = 0;
        this.cart = system.replicate(new Cart(system), JConsistencyLevel.STRONG);
    }

    public boolean Login(String userID, String password, JReplicaSystem system){
        if(!loggedInFrom.contains(system)){
            //Security is not the purpose of this case study, therefore I check passwords and userIDs like this.
            //This is not the way to check passwords in any real Program.
            if(userID.equals(this.userID) && password.equals(this.password)){
                isLoggedIn = true;
                loggedInFrom.add(system);
                return true;
            }
        }
        return false;
    }

    public boolean Logout(JReplicaSystem system){
        if(loggedInFrom.contains(system)){
            loggedInFrom.remove(system);
            return true;
        }
        return false;
    }

    public boolean SetDescription(String description,JReplicaSystem system){
        if(loggedInFrom.contains(system)){
            this.description = description;
            return true;
        }
        return false;
    }


}
