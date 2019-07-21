package de.tuda.stg.consys.shoppingcart;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;

class ErrorClass implements Serializable {
    //A class to demonstrate the error
    private JRef<@Weak ErrorSubClass> first;
    private JRef<@Weak ErrorSubClass> last;

    public void add(JReplicaSystem sys) {
        JRef<@Weak ErrorSubClass> node = sys.replicate(new ErrorSubClass(), JConsistencyLevel.WEAK);

        if(first == null) {
            first = node;
            last = first;
        }else{
            last.setField("next", node);
            last = node;
        }
    }

    public void addGivenNode(JRef<@Weak ErrorSubClass> node){
        if(first == null) {
            first = node;
            last = first;
        }else{
            last.setField("next", node);
            last = node;
        }
    }

    public void printAndSync(){
        JRef<@Weak ErrorSubClass> curr = first;
        while(curr != null){
            curr.sync();
            System.out.print("current = " + curr.toString());
            System.out.print(" , next = " + curr.getField("next") + "\n");
            curr = curr.getField("next");
        }
    }
}
