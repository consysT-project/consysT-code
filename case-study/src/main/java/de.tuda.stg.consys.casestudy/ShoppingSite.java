package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;
import java.util.LinkedList;

public class ShoppingSite implements Serializable {

    JRef<@Strong User> currentlyLoggedIn;

    JRef<@Weak Cart> CartOfLoggedIn;

    JRef<@Strong Database> Database;

    LinkedList<JRef<@Strong Product>> FoundProducts;

    ShoppingSite(JRef<@Strong Database> db) {
        Database = db;
    }

    public boolean RegisterNewUser(String UserName, String Password, JReplicaSystem system){
        if(currentlyLoggedIn != null){
            System.out.println("Cannot register a new user, you are already logged in as ''" +
                    currentlyLoggedIn.invoke("getName") +"''");
            return false;
        }

        if(Database.invoke("AddUser", UserName, Password, system))
            return Login(UserName, Password, system);

        return false;
    }

    public boolean Login(String UserName, String Password, JReplicaSystem system){
        if(currentlyLoggedIn != null){
            System.out.println("Cannot Log in, you are already logged in as ''" +
                    currentlyLoggedIn.invoke("getName") +"''");
            return false;
        }

        JRef<@Strong User> user = Database.invoke("GetUser", UserName, Password, system);
        if(user == null){
            return false;
        }
        currentlyLoggedIn = user;
        CartOfLoggedIn = currentlyLoggedIn.invoke("FetchCart", system);
        return  true;
    }

    public boolean Logout(){
        if(currentlyLoggedIn == null){
            System.out.println("Cannot Log out, you are already logged out.");
            return false;
        }

        currentlyLoggedIn.invoke("Logout");
        currentlyLoggedIn = null;
        CartOfLoggedIn = null;
        return true;
    }

    public void Search(String SearchTerm){
        FoundProducts = Database.invoke("SearchProducts", SearchTerm);

        System.out.println("Found Products:");
        for (int i = 0; i < FoundProducts.size(); i++){
            System.out.println((i + 1) + ") " + FoundProducts.get(i).invoke("getName"));
        }
    }

    public boolean FromFoundAddToCart(int number, int count, JReplicaSystem system){
        int index = number - 1;
        if(index < 0 || index >= FoundProducts.size()){
            System.out.println("Please select a valid product");
            return false;
        }

        if(CartOfLoggedIn != null)
            return CartOfLoggedIn.invoke("add", FoundProducts.get(index), count, system);
        System.out.println("You are not logged in.");
        return false;
    }

    public boolean FromFoundDisplayInfo(int number, boolean getComments){
        int index = number - 1;
        if(index < 0 || index >= FoundProducts.size()) {
            System.out.println("Please select a valid product");
            return false;
        }
        JRef<@Strong Product> currProd = FoundProducts.get(index);

        System.out.println("Name: " + currProd.invoke("getName"));
        System.out.println("Price: " + currProd.invoke("getCost"));

        if(getComments){
            System.out.println("Comments: ");
            currProd.invoke("printComments");
        }
        return true;
    }

    public boolean Checkout(JReplicaSystem system){
        if(currentlyLoggedIn == null){
            System.out.println("Please log in first");
            return false;
        }
        if(currentlyLoggedIn.invoke("verifyLogin", system)){
            return CartOfLoggedIn.invoke("checkout");
        }
        System.out.println("Please log in first");
        return false;
    }

    public boolean AddBalance(double value, JReplicaSystem system){
        if(currentlyLoggedIn != null){
            double newBalance = currentlyLoggedIn.invoke("addBalance", value, system);
            if(newBalance != Double.NaN){
                System.out.println("Money added successfully, new balance: " + newBalance);
                return true;
            }
        }
        return false;
    }
}
