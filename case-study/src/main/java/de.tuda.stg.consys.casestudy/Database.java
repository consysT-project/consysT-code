package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.jrefcollections.JRefHashMap;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.function.Predicate;

public class Database implements Serializable {

    private JRef<@Strong JRefHashMap> RegisteredUsers;

    private JRef<@Strong JRefDistList> RegisteredProducts;

    Database(JReplicaSystem system){
        RegisteredUsers = system.replicate("RegisteredUserMap", new JRefHashMap(), JConsistencyLevel.STRONG);
        RegisteredProducts = system.replicate("RegisteredObjectList", new JRefDistList(JConsistencyLevel.STRONG), JConsistencyLevel.STRONG);

    }

    public boolean AddUser(String Username, String Password, JReplicaSystem system){
        if(Username.length() < 3){
            System.out.println("A Username must be at least 3 characters long");
            if(Password.length() < 5){
                System.out.println("A Password must be at least 5 characters long");
            }
            return false;
        }

        JRef<@Strong User> currUser = RegisteredUsers.invoke("getValue", Username);
        if(currUser == null){
            JRef<@Strong User> newUser = system.replicate(new User(Username, Password, system), JConsistencyLevel.STRONG);
            RegisteredUsers.invoke("put", Username, newUser);
            return true;
        }else
            return false;
    }

    public JRef<@Strong User> GetUser(String Username, String Password, JReplicaSystem system){
        JRef<@Strong User> currUser = RegisteredUsers.invoke("getValue", Username);
        if(currUser != null) {
            if(currUser.invoke("Login", Username, Password, system)){
                return currUser;
            }
            System.out.println("Could not log in.");
            return null;
        }else{
            System.out.println("No User of the name ''" + Username + "'' found in the database.");
            return null;
        }
    }

    public LinkedList<JRef<@Strong Product>> SearchProducts(String query){
        LinkedList<JRef<@Strong Product>> retList;
        String lowerQuery = query.toLowerCase();

        Predicate<JRef<@Strong Product>> tester = productJRef -> {
            String currName = productJRef.invoke("getName");
            if(currName.toLowerCase().contains(lowerQuery))
                return true;
            return false;
        };

        retList = RegisteredProducts.invoke("getNonReplicatedSublist", tester,false);
        return retList;
    }

    public boolean AddProduct(String name, double price, JReplicaSystem system){
        Predicate<JRef<@Strong Product>> tester = productJRef -> {
            String currName = productJRef.invoke("getName");
            if(currName.toLowerCase().equals(name))
                return true;
            return false;
        };

        JRef<@Strong Product> retProduct = RegisteredProducts.invoke("search", tester, false);
        if(retProduct != null)
            return false;
        else{
            JRef<@Strong Product> newProduct = system.replicate(new Product(name, price, system), JConsistencyLevel.STRONG);
            RegisteredProducts.invoke("append", newProduct, system);
            return true;
        }
    }
}
