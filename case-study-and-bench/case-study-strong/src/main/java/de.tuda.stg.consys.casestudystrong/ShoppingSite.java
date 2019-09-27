package de.tuda.stg.consys.casestudystrong;

import de.tuda.stg.consys.casestudyinterface.IShoppingSite;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicated;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.Optional;

public class ShoppingSite implements Serializable, JReplicated, IShoppingSite {

    /* This field is needed for JReplicated */
    public transient AkkaReplicaSystem<String> replicaSystem = null;

    JRef<@Strong User> currentlyLoggedIn;

    JRef<@Strong Cart> CartOfLoggedIn;

    JRef<@Strong Database> Database;

    public JRef<@Weak JRefDistList> FoundProducts;

    public ShoppingSite(JRef<@Strong Database> db) {
        Database = db;
    }

    public boolean RegisterNewUser(String UserName, String Password){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        if(currentlyLoggedIn != null){
            System.out.println("Cannot register a new user, you are already logged in as ''" +
                    currentlyLoggedIn.invoke("getName") +"''");
            return false;
        }
        JRef<@Strong User> newUser = system.replicate(new User(UserName, Password), JConsistencyLevel.STRONG);
        newUser.invoke("init");
        if(Database.invoke("RegisterUser", UserName, Password, newUser)){
            return Login(UserName, Password);
        }
        return false;
    }

    public boolean Login(String UserName, String Password){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

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

    public boolean Logout(){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;


        if(currentlyLoggedIn == null){
            System.out.println("Cannot Log out, you are already logged out.");
            return false;
        }

        currentlyLoggedIn.invoke("Logout", system.toString());
        currentlyLoggedIn = null;
        CartOfLoggedIn = null;
        return true;
    }

    public JRef<@Weak JRefDistList> Search(String SearchTerm, boolean printResults){
        FoundProducts = Database.invoke("SearchProducts", SearchTerm);

        if(printResults) {
            System.out.println("Found Products:");
            for (int i = 0; i < (int) FoundProducts.invoke("size", true); i++) {
                System.out.println((i + 1) + ") " +
                        ((JRef<@Strong Product>) FoundProducts.invoke("getIndex", i, true))
                                .invoke("getName"));
            }
        }
        return FoundProducts;
    }



    public boolean FromFoundAddToCart(int number, int count){
        int index = number - 1;
        if(index < 0 || index >= (int) FoundProducts.invoke("size", true)){
            System.out.println("Please select a valid product");
            return false;
        }
        if(CartOfLoggedIn != null){
            CartOfLoggedIn.invoke("add", FoundProducts.invoke("getIndex", index, true), count);
            return true;
        }
        System.out.println("You are not logged in.");
        return false;
    }

    public String FromFoundDisplayInfo(int number, boolean getComments, boolean printInfo){
        int index = number - 1;
        String ret;
        if(index < 0 || index >= (int) FoundProducts.invoke("size", true)) {
            ret = "Please select a valid product";
        }
        else{
            JRef<@Strong Product> currProd = FoundProducts.invoke("getIndex", index, true);

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

    public boolean Checkout(boolean PrintReceipt){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        if(currentlyLoggedIn == null){
            System.out.println("Please log in first");
            return false;
        }
        if(currentlyLoggedIn.invoke("verifyLogin", system.toString())){
            return CartOfLoggedIn.invoke("checkout", currentlyLoggedIn, PrintReceipt, system.toString());
        }
        System.out.println("Please log in first");
        return false;
    }

    public double AddBalance(double value, boolean PrintBalance){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return Double.NaN;

        if(currentlyLoggedIn != null){
            double newBalance = currentlyLoggedIn.invoke("addBalance", value, system.toString());
            if(!Double.isNaN(newBalance)){
                if(PrintBalance)
                    System.out.println("Money added successfully, new balance: " + newBalance);
                return newBalance;
            }
        }
        return Double.NaN;
    }
}
