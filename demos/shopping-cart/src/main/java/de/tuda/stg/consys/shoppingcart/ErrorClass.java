package de.tuda.stg.consys.shoppingcart;

import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicated;

import java.io.Serializable;
import java.util.Optional;

class ErrorClass implements Serializable, JReplicated {

    /* This field is needed for JReplicated */
    public transient AkkaReplicaSystem<String> replicaSystem = null;


    //A class to demonstrate the error
    private JRef<@Weak ErrorSubClass> first;
    private JRef<@Weak ErrorSubClass> last;

    public void add(JReplicaSystem sys) {
        JRef<@Weak ErrorSubClass> node = sys.replicate(new ErrorSubClass(), JConsistencyLevels.WEAK);

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

    public boolean createInternal(){

        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        system.replicate(new InternalSubClass(), JConsistencyLevels.STRONG);

        return false;
    }

    public void takeArray(Object[] array){
        System.out.println("Took array");
    }


    public void takeStrArray(String[] array){
        System.out.println("Took array");
    }

    class InternalSubClass implements Serializable{

    }
}
