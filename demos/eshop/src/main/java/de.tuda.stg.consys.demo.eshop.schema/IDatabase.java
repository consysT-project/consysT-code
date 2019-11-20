package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.objects.japi.JRef;

import java.util.ArrayList;

/*
Interface for the database class of the case study
 */
public interface IDatabase<User, List> {

    public boolean init(int initUserCount, int initProductCount);


    /*
     * Function to be called when directly invoking the database
     */
    public boolean addUser(String Username, String Password);

    /*
     * Function to be called during indirect invocation (i.e. through the shopping site)
     */
    public boolean registerUser(String Username, String Password, JRef<User> newUser);

    public JRef<User> GetUser(String Username, String Password, String systemInfo);

    /*
    Delete User from database
     */
    public ArrayList<JRef> deleteUser(String Username);

    public JRef searchProducts(String query, int limit);

    /*
     * Function to add several products at once without checking for duplicate products
     * add initial list of products as semicolon seperated Name and price
     */
    public boolean addInitialProducts(ArrayList<String> prods);

    /*
     * Add Singular Product to Database
     * Checks for types & if the product is already in the database
     */
    public boolean addProduct(String name, double price);
}
