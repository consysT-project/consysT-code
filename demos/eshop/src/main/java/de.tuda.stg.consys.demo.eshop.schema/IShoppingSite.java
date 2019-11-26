package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.examples.collections.JRefDistList;
import de.tuda.stg.consys.japi.JRef;

import java.util.ArrayList;

/*
Interface for the shopping site class of the case study
 */
public interface IShoppingSite<T> {

    boolean RegisterNewUser(String UserName, String Password);

    boolean login(String UserName, String Password);

    boolean Logout();

    JRef<@Weak JRefDistList> Search(String SearchTerm, boolean printResults, int limit);

    boolean FromFoundAddToCart(int number, int count);

    String FromFoundDisplayInfo(int number, boolean getComments, boolean printInfo);

    boolean Checkout(boolean PrintReceipt);

    double addBalance(double value, boolean PrintBalance);

    ArrayList<JRef> ClearCart();
}
