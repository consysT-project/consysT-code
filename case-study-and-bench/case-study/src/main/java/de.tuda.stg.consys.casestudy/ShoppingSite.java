package de.tuda.stg.consys.casestudy;

import com.sun.tools.javac.util.ArrayUtils;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.DistNode;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import org.checkerframework.com.google.common.collect.ObjectArrays;

import java.io.Serializable;
import java.util.LinkedList;

public class ShoppingSite implements Serializable {

    JRef<@Strong User> currentlyLoggedIn;

    JRef<@Weak Cart> CartOfLoggedIn;

    JRef<@Strong Database> Database;

    public LinkedList<JRef<@Strong Product>> FoundProducts;

    public ShoppingSite(JRef<@Strong Database> db) {
        Database = db;
    }

    public boolean RegisterNewUser(String UserName, String Password, JReplicaSystem system){
        if(currentlyLoggedIn != null){
            System.out.println("Cannot register a new user, you are already logged in as ''" +
                    currentlyLoggedIn.invoke("getName") +"''");
            return false;
        }
        JRef<@Strong User> newUser = system.replicate(new User(UserName, Password, system), JConsistencyLevel.STRONG);
        if(Database.invoke("RegisterUser", UserName, Password, newUser)){
            return Login(UserName, Password, system);
        }
        return false;
    }

    public boolean Login(String UserName, String Password, JReplicaSystem system){
        if(currentlyLoggedIn != null){
            System.out.println("Cannot Log in, you are already logged in as ''" +
                    currentlyLoggedIn.invoke("getName") +"''");
            return false;
        }
        JRef<@Strong User> user = Database.invoke("GetUser", UserName, Password, system.toString());

        if(user == null){
            return false;
        }

        currentlyLoggedIn = user;
        CartOfLoggedIn = currentlyLoggedIn.invoke("FetchCart", system.toString());
        return  true;
    }

    public boolean Logout(JReplicaSystem system){
        if(currentlyLoggedIn == null){
            System.out.println("Cannot Log out, you are already logged out.");
            return false;
        }

        currentlyLoggedIn.invoke("Logout", system.toString());
        currentlyLoggedIn = null;
        CartOfLoggedIn = null;
        return true;
    }

    public LinkedList<JRef<Product>> Search(String SearchTerm, boolean printResults){
        FoundProducts = Database.invoke("SearchProducts", SearchTerm);

        if(printResults) {
            System.out.println("Found Products:");
            for (int i = 0; i < FoundProducts.size(); i++) {
                System.out.println((i + 1) + ") " + FoundProducts.get(i).invoke("getName"));
            }
        }
        return FoundProducts;
    }



    public boolean FromFoundAddToCart(int number, int count, JReplicaSystem system){
        int index = number - 1;
        if(index < 0 || index >= FoundProducts.size()){
            System.out.println("Please select a valid product");
            return false;
        }
        if(CartOfLoggedIn != null){
            for(int x = 0;x < count;x++){
                JRef<@Weak DistNode> newNode = system.replicate(new DistNode(FoundProducts.get(index)), JConsistencyLevel.WEAK);
                CartOfLoggedIn.invoke("addNode", newNode);
            }
            //CartOfLoggedIn.invoke("add", FoundProducts.get(index), count, system);
            return true;
        }
        System.out.println("You are not logged in.");
        return false;
    }

    public String FromFoundDisplayInfo(int number, boolean getComments, boolean printInfo){
        int index = number - 1;
        String ret;
        if(index < 0 || index >= FoundProducts.size()) {
            ret = "Please select a valid product";
        }
        else{
            JRef<@Strong Product> currProd = FoundProducts.get(index);


            ret = currProd.invoke("getName");
            ret += currProd.invoke("getCost");

            if(getComments){
                String comments = currProd.invoke("getComments");
                ret += comments;
            }
        }
        if(printInfo)
            System.out.println(ret);

        return ret;
    }

    public boolean Checkout(JReplicaSystem system, boolean PrintReceipt){
        if(currentlyLoggedIn == null){
            System.out.println("Please log in first");
            return false;
        }
        if(currentlyLoggedIn.invoke("verifyLogin", system.toString())){
            return CartOfLoggedIn.invoke("checkout", currentlyLoggedIn ,PrintReceipt, system.toString());
        }
        System.out.println("Please log in first");
        return false;
    }

    public double AddBalance(double value, JReplicaSystem system, boolean PrintBalance){
        if(currentlyLoggedIn != null){
            double newBalance = currentlyLoggedIn.invoke("addBalance", value, system.toString());
            if(newBalance != Double.NaN){
                if(PrintBalance)
                    System.out.println("Money added successfully, new balance: " + newBalance);
                return newBalance;
            }
        }
        return Double.NaN;
    }
}
