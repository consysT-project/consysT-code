package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;
import java.util.HashSet;
import java.util.Set;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Class of a Dot-Store. Consists of an Context that tells which Dot is
 * assisiated with which Event, a store for all Dots and a (String) Set
 * for the actual elements that should be stored
 */
public class DotStoreString extends DeltaCRDT implements Serializable {


    public List<Pair<Event,Dot>> context;

    public Set<Dot> store;

    public Set<String> stringset;

    /**
     * Constructor
     */
    public DotStoreString() {
        context = new LinkedList<>();
        store = new HashSet<>();
       stringset = new HashSet<>();
    }

    /**
     *
     * @param id ID of the Dot
     * @return the current maximum sequence number of the dot with the given ID
     */
    public int max(int id) {
        int x = -1;
        int k ;
        int v;
        //get maximum sequence
        //change concurrent thingy
        for(int i = 0; i < context.size(); i++){
            if(context.get(i).getValue().dot.getKey() == id){
                k = context.get(i).getValue().dot.getValue();
                if(k > x){
                    x = k;
                }
            }
        }
       // System.out.println("called max");
        return x;
    }

    /**
     *
     * @param id ID of the dot
     * @return the next sequence number of the dot with the given ID
     */
    public int next(int id) {
        //next sequence number
        return this.max(id) + 1;
    }


    /**
     * adds a String to the Dot-Store
     * @param s String that should be added
     * @param id ID of the Dot
     * @return a Delta Object with an Add-Event associated with a Dot
     */
    public Delta addString(String s, int id) {
        int next = this.next(id);
        Dot dot = new Dot(id, next);
        Add add = new Add(s);

        Pair<Event, Dot> p = new Pair<>(add, dot);
        context.add(p);
        store.add(dot);
        stringset.add(s);
        return new Delta(p);
    }

    /**
     * removes a String to the Dot-Store
     * @param s String that should be removed
     * @param id ID of the Dot
     * @return a Delta Object with an Remove-Event associated with a Dot
     */
    public Delta removeString(String s, int id){
        int next = this.next(id);
        Dot dot = new Dot(id,next);
        Remove rem = new Remove(s);

        Pair<Event,Dot> p = new Pair<>(rem,dot);
        context.add(p); //context is grow only
        store.remove(dot);
        stringset.remove(s);
        return new Delta(p);
    }


    /**
     * merges incoming delta messages with the current Dot-Store
     * @param other Delta message
     */
    @Override
    public void merge(Object other) {
        if (other instanceof Pair) {
            Pair<Event,Dot> p = (Pair<Event,Dot>) other;
            Event e = p.getKey();
            Dot d = p.getValue();
            if(e instanceof Add){
                Add a = (Add) e;
                store.add(d);
                stringset.add(a.element);
            }else if (e instanceof Remove){
                Remove r = (Remove) e ;
                store.remove(d);
                stringset.remove(r.element);
            }

        }
    }

    @Override
    public String toString() {
            String s = "";
            for (String k : stringset){
                s = s + k + ",";
            }
            return s;
    }
}

