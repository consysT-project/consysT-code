package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.casestudyinterface.IDatabase;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.JRefAddressMap;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.jrefcollections.JRefHashMap;
import de.tuda.stg.consys.objects.ConsistencyLevel;
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicated;

import java.io.*;
import java.util.ArrayList;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.function.Predicate;

public class Database implements Serializable , JReplicated, IDatabase<@Strong User,@Strong Product> {

    /* This field is needed for JReplicated */
    public transient AkkaReplicaSystem<String> replicaSystem = null;

    private JRef<@Strong JRefAddressMap> RegisteredUsers;

    private JRef<@Strong JRefDistList> RegisteredProducts;

    public Database()throws NoSuchElementException {
    }

    public void test(){
        RegisteredUsers.invoke("touchAll");
    }

    public boolean init(int initUserCount, int initProductCount){

        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        RegisteredUsers = system.replicate("RegisteredUserMap", new JRefAddressMap(), JConsistencyLevel.STRONG);
        RegisteredUsers.invoke("init", initUserCount, JConsistencyLevel.STRONG);
        RegisteredProducts = system.replicate("RegisteredObjectList", new JRefDistList(JConsistencyLevel.STRONG), JConsistencyLevel.STRONG);
        return true;
    }


    /*
     * Function to be called when directly invoking the database
     */
    public boolean AddUser(String Username, String Password){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        JRef<@Strong User> newUser = system.replicate(new User(Username, Password), JConsistencyLevel.STRONG);
        newUser.invoke("init");
        return RegisterUser(Username, Password, newUser);
    }

    /*
     * Function to be called during indirect invocation (i.e. through the shopping site)
     */
    public boolean RegisterUser(String Username, String Password, JRef<@Strong User> newUser){
        if(Username.length() < 3){
            System.out.println("A Username must be at least 3 characters long");
            if(Password.length() < 5){
                System.out.println("A Password must be at least 5 characters long");
            }
            return false;
        }
        if(!((boolean) newUser.invoke("verifyCredentials", Username, Password))){
            System.out.println("Something went wrong!");
            return false;
        }

        String currUserAddr = RegisteredUsers.invoke("getValue", Username);
        if(currUserAddr == null){
            RegisteredUsers.invoke("put", Username, newUser);
            return true;
        }else
            return false;
    }

    public JRef<@Strong User> GetUser(String Username, String Password, String systemInfo){
        String addr = RegisteredUsers.invoke("getValue", Username);
        JRef<@Strong User> currUser = resolveUser(addr, JConsistencyLevel.STRONG);
        if(currUser != null) {
            boolean loggedIn = currUser.invoke("Login", Username, Password, systemInfo);
            if(loggedIn){
                return currUser;
            }
            System.out.println("Could not log in.");
            return null;
        }else{
            System.out.println("No User of the name ''" + Username + "'' found in the database.");
            return null;
        }
    }

    public JRef<@Weak JRefDistList> SearchProducts(String query){
        String lowerQuery = query.toLowerCase();
        JRef<@Weak JRefDistList> retList = null;

        Predicate<JRef<@Strong Product>> tester = (Predicate<JRef<@Strong Product>> & Serializable) productJRef -> {
            String currName = productJRef.invoke("getName");
            if(currName.toLowerCase().contains(lowerQuery))
                return true;
            return false;
        };
        System.out.println("Reached before the getWeakReplicaSublistInvocation");
        retList = RegisteredProducts.invoke("getWeakReplicaSublist", tester, 1000,true);
        System.out.println("Reached after the getweakreplicasublist invocation");
        return retList;
    }

    /*
     * Function to add several products at once without checking for duplicate products
     * add initial list of products as semicolon seperated Name and price
     */
    public boolean AddInitialProducts(ArrayList<String> prods){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;
        if(prods.size() < 1)
            return false;

        for (String prod: prods) {
            String[] split = new String[0];
            double price = 0; boolean skip = false;
            try{
                split = prod.split(";");
                price = Double.parseDouble(split[1]);
            }
            catch (Exception e){
                System.out.println("Invalid Product, Skipping.");
                skip = true;
            }
            if(!skip){
                JRef<@Strong Product> newProduct = system.replicate(new Product(split[0], price), JConsistencyLevel.STRONG);
                newProduct.invoke("init");

                RegisteredProducts.invoke("append", newProduct);
            }
        }
        return true;
    }

    /*
     * Add Singular Product to Database
     * Checks for types & if the product is already in the database
     */
    public boolean AddProduct(String name, double price){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        Predicate<JRef<@Strong Product>> tester = (Predicate<JRef<@Strong Product>> & Serializable) productJRef -> {
            String currName = productJRef.invoke("getName");
            if(currName.toLowerCase().equals(name))
                return true;
            return false;
        };

        JRef<@Strong Product> retProduct = RegisteredProducts.invoke("search", tester, false);
        if(retProduct != null)
            return false;
        else{
            JRef<@Strong Product> newProduct = system.replicate(new Product(name, price), JConsistencyLevel.STRONG);
            newProduct.invoke("init");
            RegisteredProducts.invoke("append", newProduct);
            return true;
        }
    }

    private JRef<User> resolveUser(String addr, ConsistencyLevel level){
        if(addr == null)return null;

        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return null;

        return system.ref(addr, User.class, level);
    }

    private JRef<Product> resolveProduct(String addr, ConsistencyLevel level){
        if(addr == null)return null;

        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return null;

        return system.ref(addr, Product.class, level);
    }
}


