package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.eshop.EShopLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedList;

public class User implements Serializable {

    private String userID;

    private String password;

    private LinkedList<String> loggedInFrom;

    private String description;

    private double balance;

    private JRef<@Weak Cart> cart;

    private LinkedList<JRef<@Weak Product>> buyHistory;

    User(String userID, String password){
        this.userID = userID; this.password = password;
        loggedInFrom = new LinkedList<String>();
        balance = 0;
        buyHistory = new LinkedList<JRef<@Weak Product>>();
    }

    public boolean init(){
        JReplicaSystem system = JReplicaSystems.getSystem();

        this.cart = system.replicate(new Cart(system),  EShopLevels.getStrongLevel());
        return true;
    }

    public boolean Login(String userID, String password, String systemInfo){
        boolean ret = false;
        if(!loggedInFrom.contains(systemInfo)){
            //Security is not the purpose of this case study, therefore I check passwords and userIDs like this.
            //This is not the way to check passwords in any real Program.
            if(userID.equals(this.userID) && password.equals(this.password)){
                loggedInFrom.add(systemInfo);
                ret = true;
            }
        }
        return ret;
    }

    public boolean Logout(String systemInfo){
        if(loggedInFrom.contains(systemInfo)){
            loggedInFrom.remove(systemInfo);
            return true;
        }
        return false;
    }

    public boolean SetDescription(String description,String systemInfo){
        if(loggedInFrom.contains(systemInfo)){
            this.description = description;
            return true;
        }
        return false;
    }

    public JRef<@Strong Cart> FetchCart(String systemInfo){
        if(loggedInFrom.contains(systemInfo)){
            return cart;
        }
        else return null;
    }

    public boolean verifyLogin(String systemInfo){
        return loggedInFrom.contains(systemInfo);
    }

    public boolean verifyCredentials(String Username, String Password) {
        return Username.equals(userID) && Password.equals(this.password);
    }

    public String getName(){
        return userID;
    }

    public String getDescription(){
        return description;
    }

    public boolean buy(double cost, LinkedList<JRef<@Weak Product>> products, String systemInfo){
        if(loggedInFrom.contains(systemInfo)){
            if(cost <= balance){
                buyHistory.addAll(products);
                balance -= cost;
                return true;
            }
        }
        return false;
    }

    public double addBalance(double balance, String systemInfo){
        if(loggedInFrom.contains(systemInfo)){
            if(balance > 0){
                this.balance += balance;
                return this.balance;
            }
            return Double.NaN;
        }
        else return Double.NaN;
    }

    public ArrayList<JRef> getForDelete(){
        return new ArrayList<>(cart.ref().getForDelete());
    }
}
