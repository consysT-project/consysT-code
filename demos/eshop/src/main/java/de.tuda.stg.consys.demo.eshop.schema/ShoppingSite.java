package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.demo.eshop.EShopLevels;
import de.tuda.stg.consys.examples.collections.JRefArrayList;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.JReplicated;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Optional;

public class ShoppingSite implements Serializable, JReplicated, IShoppingSite {

    /* This field is needed for JReplicated */
    public transient AkkaReplicaSystem replicaSystem = null;

    private JRef<@Strong User> currentlyLoggedIn;

    private JRef<@Weak Cart> cartOfLoggedIn;

    private JRef<@Weak Database> database;

    private JRef<@Weak JRefArrayList> foundProducts;

    public ShoppingSite(JRef<@Weak Database> db) {
        database = db;
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
                    currentlyLoggedIn.ref().getName() +"''");
            return false;
        }
        JRef<@Strong User> newUser = system.replicate(new User(UserName, Password), EShopLevels.getStrongLevel());
        newUser.ref().init();
        if(database.ref().registerUser(UserName, Password, newUser)){
            return login(UserName, Password);
        }
        return false;
    }

    public boolean login(String UserName, String Password){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        if(currentlyLoggedIn != null){
            System.out.println("Cannot Log in, you are already logged in as ''" +
                    currentlyLoggedIn.ref().getName() +"''");
            return false;
        }
        JRef<@Strong User> user = database.ref().GetUser(UserName, Password, system.toString());

        if(user == null){
            return false;
        }

        currentlyLoggedIn = user;
        cartOfLoggedIn = currentlyLoggedIn.ref().FetchCart(system.toString());
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

        currentlyLoggedIn.ref().Logout(system.toString());
        currentlyLoggedIn = null;
        cartOfLoggedIn = null;
        return true;
    }

    public JRef<@Weak JRefArrayList> Search(String SearchTerm, boolean printResults, int limit){
        foundProducts = database.ref().searchProducts(SearchTerm, limit);

        if(printResults) {
            System.out.println("Found Products:");
            for (int i = 0; i < (int) foundProducts.ref().size(true); i++) {
                System.out.println((i + 1) + ") " +
                        ((JRef<@Weak Product>) foundProducts.invoke("getIndex", i, true))
                        .invoke("getName"));
            }
        }
        return foundProducts;
    }



    public boolean FromFoundAddToCart(int number, int count){
        int index = number - 1;

        if (foundProducts == null)
            return false;

        int allowed = (int) foundProducts.ref().size(true);
        if(index < 0 || index >= allowed){
            System.out.println("Please select a valid product, Chose " + index + " out of " + allowed);
            return false;
        }
        if(cartOfLoggedIn != null){
            JRef<Product> product = foundProducts.ref().getIndex(index, true);
            cartOfLoggedIn.ref().add(product, count);
            return true;
        }
        System.out.println("You are not logged in.");
        return false;
    }

    public String FromFoundDisplayInfo(int number, boolean getComments, boolean printInfo){
        int index = number - 1;

        if (foundProducts == null)
            return "Please do a search first";

        if(index < 0 || index >= (int) foundProducts.ref().size(true))
            return "Please select a valid product";

        String ret;

        JRef<@Weak Product> currProd = foundProducts.ref().getIndex(index, true);

        ret = currProd.ref().getName();
        ret += currProd.ref().getCost();

        if(getComments){
            String comments = currProd.ref().getComments();
            ret += comments;
        }

        if(printInfo) System.out.println(ret);

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
        if(currentlyLoggedIn.ref().verifyLogin(system.toString())){
            return cartOfLoggedIn.ref().checkout(currentlyLoggedIn, PrintReceipt, system.toString());
        }
        System.out.println("Please log in first");
        return false;
    }

    public double addBalance(double value, boolean PrintBalance){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return Double.NaN;

        if(currentlyLoggedIn != null){
            double newBalance = currentlyLoggedIn.ref().addBalance(value, system.toString());
            if(!Double.isNaN(newBalance)){
                if(PrintBalance)
                    System.out.println("Money added successfully, new balance: " + newBalance);
                return newBalance;
            }
        }
        return Double.NaN;
    }

    public ArrayList<JRef> ClearCart(){
        ArrayList<JRef> retArray = new ArrayList<>();
        if(cartOfLoggedIn != null){
            retArray.addAll(cartOfLoggedIn.ref().getForDelete());
        }
        return retArray;
    }
}
