package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.japi.legacy.JRef;

import java.util.ArrayList;
import java.util.Collection;

/*
Interface for the database class of the case study
 */
public interface IDatabase<User, List> {

    boolean init(int initUserCount, int initProductCount);


    /*
     * Function to be called when directly invoking the database
     */
	boolean addUser(String Username, String Password);

    /*
     * Function to be called during indirect invocation (i.e. through the shopping site)
     */
	boolean registerUser(String Username, String Password, JRef<User> newUser);

    JRef<User> GetUser(String Username, String Password, String systemInfo);

    /*
    Delete User from database
     */
	ArrayList<JRef> deleteUser(String Username);

    JRef searchProducts(String query, int limit);

    /*
     * Function to add several products at once without checking for duplicate products
     * add initial list of products as semicolon seperated Name and price
     */
	boolean addInitialProducts(Collection<String> prods);

    /*
     * Add Singular Product to Database
     * Checks for types & if the product is already in the database
     */
	boolean addProduct(String name, double price);
}
