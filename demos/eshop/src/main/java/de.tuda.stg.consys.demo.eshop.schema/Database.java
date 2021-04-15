package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.legacy.ConsistencyLabel;
import de.tuda.stg.consys.demo.eshop.EShopLevels;
import de.tuda.stg.consys.examples.collections.JRefArrayList;
import de.tuda.stg.consys.examples.collections.JRefArrayMap;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.NoSuchElementException;
import java.util.function.Predicate;

public class Database implements Serializable, IDatabase<User, Product> {

    private JRef<@Strong JRefArrayMap> registeredUsers;

    private JRef<@Weak JRefArrayList> registeredProducts;

    private final int mapArraySize;
    private final int listArraySize;

    public Database(int MapArraySize, int ListArraySize)throws NoSuchElementException {
        this.mapArraySize = MapArraySize;
        this.listArraySize = ListArraySize;
    }

    public int syncProds() {
        return registeredProducts.ref().size( true);
    }

    public boolean init(int initUserCount, int initProductCount){

        JReplicaSystem system = JReplicaSystems.getSystem();

        registeredUsers = system.replicate("RegisteredUserMap", new JRefArrayMap(initUserCount, mapArraySize, EShopLevels.getStrongLevel()), EShopLevels.getStrongLevel());

        registeredProducts = system.replicate("RegisteredObjectList",
                new JRefArrayList(EShopLevels.getWeakLevel(), listArraySize), EShopLevels.getWeakLevel());

        return true;
    }


    /*
     * Function to be called when directly invoking the database
     */
    public boolean addUser(String Username, String Password){
        JReplicaSystem system = JReplicaSystems.getSystem();

        JRef<@Strong User> newUser = system.replicate(new User(Username, Password), EShopLevels.getStrongLevel());
        newUser.ref().init();
        return registerUser(Username, Password, newUser);
    }

    /*
    Delete User from database
     */
    public ArrayList<JRef> deleteUser(String Username){
        JReplicaSystem system = JReplicaSystems.getSystem();

        String user = registeredUsers.ref().remove(Username);
        if(user != null){
            JRef<@Strong User> userJRef = system.lookup(user,User.class, EShopLevels.getStrongLevel());
            ArrayList<JRef> retArray = userJRef.ref().getForDelete();
            return retArray;
        }
        return null;
    }

    /*
     * Function to be called during indirect invocation (i.e. through the shopping site)
     */
    public boolean registerUser(String Username, String Password, JRef<@Strong User> newUser){
        if(Username.length() < 3){
            System.out.println("A Username must be at least 3 characters long");
            if(Password.length() < 5){
                System.out.println("A Password must be at least 5 characters long");
            }
            return false;
        }
        if(!((boolean) newUser.ref().verifyCredentials(Username, Password))){
            System.out.println("Something went wrong!");
            return false;
        }

        String currUserAddr = registeredUsers.ref().getValue( Username);
        if(currUserAddr == null){
            registeredUsers.ref().put(Username, newUser);
            return true;
        }else
            return false;
    }

    public JRef<@Strong User> GetUser(String Username, String Password, String systemInfo){
        String addr = registeredUsers.ref().getValue(Username);
        JRef<@Strong User> currUser = resolveUser(addr, EShopLevels.getStrongLevel());
        if(currUser != null) {
            boolean loggedIn = currUser.ref().Login(Username, Password, systemInfo);
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

    public JRef<JRefArrayList> searchProducts(String query, int limit){
        String lowerQuery = query.toLowerCase();

        Predicate<JRef<Product>> tester = (Predicate<JRef<Product>> & Serializable) productJRef -> {
            productJRef.sync();
            String currName = productJRef.ref().getName();
            return currName.toLowerCase().contains(lowerQuery);
        };

        registeredProducts.sync();
        return registeredProducts.ref().getWeakReplicaSublist(tester, limit,true);
    }

    /*
     * Function to add several products at once without checking for duplicate products
     * add initial list of products as semicolon seperated Name and price
     */
    public boolean addInitialProducts(Collection<String> prods){
        JReplicaSystem system = JReplicaSystems.getSystem();

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
                /*
                    The approach of using a Hashmap to store substrings was abandoned, due to RAM limitations.
                 */
                JRef<@Weak Product> newProduct = system.replicate(new Product(split[0], price), EShopLevels.getWeakLevel());
                newProduct.ref().init();
                registeredProducts.sync();
                registeredProducts.ref().append(newProduct);
                System.out.print("\rAdded Product: " + split[0].substring(0, Math.min(split[0].length(), 20)) + "...");
            }
        }
        System.out.println();
        return true;
    }







    /*
     * Add Singular Product to Database
     * Checks for types & if the product is already in the database
     */
    public boolean addProduct(String name, double price){
        JReplicaSystem system = JReplicaSystems.getSystem();

        Predicate<JRef<Product>> tester = (Predicate<JRef<Product>> & Serializable) productJRef -> {
            String currName = productJRef.ref().getName();
            return currName.toLowerCase().equals(name);
        };

        JRef<Product> retProduct = registeredProducts.ref().search(tester, true);

        if(retProduct != null)
            return false;
        else{
            JRef<Product> newProduct = system.replicate(new Product(name, price), EShopLevels.getWeakLevel());
            newProduct.ref().init();
            registeredProducts.ref().append(newProduct);
            return true;
        }
    }

    private JRef<User> resolveUser(String addr, ConsistencyLabel level){
        if(addr == null)return null;

        JReplicaSystem system = JReplicaSystems.getSystem();

        return system.lookup(addr, User.class, level);
    }

    private JRef<Product> resolveProduct(String addr, ConsistencyLabel level){
        if(addr == null)return null;

        JReplicaSystem system = JReplicaSystems.getSystem();

        return system.lookup(addr, Product.class, level);
    }
}


