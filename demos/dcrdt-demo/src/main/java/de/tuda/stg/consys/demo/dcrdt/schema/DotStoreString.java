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
        for(int i = 0; i < context.size(); i++){
            if(context.get(i).getValue().dot.getKey() == id){
                k = context.get(i).getValue().dot.getValue();
                if(k > x){
                    x = k;
                }
            }
        }
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
        stringset.add(s);
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
                int id = d.dot.getKey();
                int seqNr = d.dot.getValue();
                if(findElement(id,a.element)<seqNr) {
                    store.add(d);
                }

                stringset.add(a.element);
            }else if (e instanceof Remove){
                Remove r = (Remove) e ;
                int id = d.dot.getKey();
                int seqNr = d.dot.getValue();
                if(findElement(id,r.element)<seqNr && findElement(id,r.element) != -1) {
                    store.remove(d);
                }
                stringset.add(r.element);
            }

        }
    }

    /**
     * checks if the given String is currently element of the store
     * @param id id of the dot
     * @param s String that is checked
     * @return the sequence number of the last addition or
     * -1 if it is removed/not present in the dot
     */
    public int findElement(int id, String s){
       LinkedList<Pair<Event,Dot>> idList = new LinkedList<>();
        //searches for all Dots with the given id
       for (int i = 0; i< context.size(); i++){
           if(context.get(i).getValue().dot.getKey() == id){
               idList.add(context.get(i));
           }
       }

       int max = 0;
       int found = -1;
       for(int j = 0; j< idList.size(); j++){
           Pair<Event,Dot> p = idList.get(j);
           Event e = p.getKey();
           if( e instanceof Add){
               Add a = (Add) e;
               if(a.element.equals(s)){
                   if(p.getValue().dot.getValue()>max){

                       max = p.getValue().dot.getValue();
                       found = max;
                   }
               }
           }else if (e instanceof Remove){
               Remove r = (Remove) e ;
               if(r.element.equals(s)){
                   if(p.getValue().dot.getValue()>max){
                       found = -1;
                       max = p.getValue().dot.getValue();
                   }
               }
           }
       }

        return found;
    }

    /**
     *
     * @param id id of the replica
     * @return a Set with all Strings, that the replica currently contains
     */
    public Set<String> getSet(int id) {
        Set<String> s = new HashSet<>();
        for (String k : stringset) {
            if (findElement(id, k) >= 0) {
                s.add(k);
            }
        }
        return s;

    }

    /**
     *
     * @param id id of the replica
     * @return the strings that the replica contains currently
     */
    public String toString(int id) {
            String s = "";
            for (String k : stringset){
                if(findElement(id,k)>=0) {
                    s = s + k + ",";
                }
            }
            return s;
    }
}

