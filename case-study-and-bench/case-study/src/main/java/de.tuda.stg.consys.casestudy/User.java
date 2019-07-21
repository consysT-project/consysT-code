package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.util.LinkedList;

public class User {

    private String userID;

    private String password;

    private LinkedList<JReplicaSystem> loggedInFrom;

    private String description;

    private double balance;

    private JRef<@Weak Cart> cart;

    private LinkedList<JRef<@Strong Product>> buyHistory;

    User(String userID, String password, JReplicaSystem system){
        this.userID = userID; this.password = password;
        loggedInFrom = new LinkedList<JReplicaSystem>();
        balance = 0;
        this.cart = system.replicate(new Cart(system), JConsistencyLevel.STRONG);
    }

    public boolean Login(String userID, String password, JReplicaSystem system){
        if(!loggedInFrom.contains(system)){
            //Security is not the purpose of this case study, therefore I check passwords and userIDs like this.
            //This is not the way to check passwords in any real Program.
            if(userID.equals(this.userID) && password.equals(this.password)){
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

    public JRef<@Strong Cart> FetchCart(JReplicaSystem system){
        if(loggedInFrom.contains(system)){
            return cart;
        }
        else return null;
    }

    public boolean verifyLogin(JReplicaSystem system){
        if(loggedInFrom.contains(system)){
            return true;
        }
        return false;
    }

    public String getName(){
        return userID;
    }

    public String getDescription(){
        return description;
    }

    public boolean buy(double cost, LinkedList<JRef<@Strong Product>> products, JReplicaSystem system){
        if(loggedInFrom.contains(system)){
            if(cost <= balance){
                buyHistory.addAll(products);
                balance -= cost;
                return true;
            }
        }
        return false;
    }

    public double addBalance(double balance, JReplicaSystem system){
        if(loggedInFrom.contains(system)){
            if(balance > 0){
                this.balance = balance;
                return this.balance;
            }
            return Double.NaN;
        }
        else
            return Double.NaN;
    }
}
