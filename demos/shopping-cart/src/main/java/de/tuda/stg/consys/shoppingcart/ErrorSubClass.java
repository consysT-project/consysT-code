package de.tuda.stg.consys.shoppingcart;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;

class ErrorSubClass implements Serializable {
    //A sub class to demonstrate the error
    public JRef<@Weak ErrorSubClass> next;



    ErrorSubClass(){}


}