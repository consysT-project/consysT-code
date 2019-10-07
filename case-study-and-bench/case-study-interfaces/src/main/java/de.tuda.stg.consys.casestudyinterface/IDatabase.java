package de.tuda.stg.consys.casestudyinterface;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.jrefcollections.JRefDistList;
import de.tuda.stg.consys.objects.japi.JRef;

import java.util.ArrayList;

/*
Interface for the database class of the case study
 */
public interface IDatabase<T,U> {

    public boolean init(int initUserCount, int initProductCount);


    /*
     * Function to be called when directly invoking the database
     */
    public boolean AddUser(String Username, String Password);

    /*
     * Function to be called during indirect invocation (i.e. through the shopping site)
     */
    public boolean RegisterUser(String Username, String Password, JRef<T> newUser);

    public JRef<T> GetUser(String Username, String Password, String systemInfo);

    public JRef SearchProducts(String query, int limit);

    /*
     * Function to add several products at once without checking for duplicate products
     * add initial list of products as semicolon seperated Name and price
     */
    public boolean AddInitialProducts(ArrayList<String> prods);

    /*
     * Add Singular Product to Database
     * Checks for types & if the product is already in the database
     */
    public boolean AddProduct(String name, double price);
}
