package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.examples.collections.JRefDistList;
import de.tuda.stg.consys.objects.japi.JRef;

import java.util.ArrayList;

/*
Interface for the shopping site class of the case study
 */
public interface IShoppingSite<T> {

    public boolean RegisterNewUser(String UserName, String Password);

    public boolean login(String UserName, String Password);

    public boolean Logout();

    public JRef<@Weak JRefDistList> Search(String SearchTerm, boolean printResults, int limit);

    public boolean FromFoundAddToCart(int number, int count);

    public String FromFoundDisplayInfo(int number, boolean getComments, boolean printInfo);

    public boolean Checkout(boolean PrintReceipt);

    public double AddBalance(double value, boolean PrintBalance);

    public ArrayList<JRef> ClearCart();
}
