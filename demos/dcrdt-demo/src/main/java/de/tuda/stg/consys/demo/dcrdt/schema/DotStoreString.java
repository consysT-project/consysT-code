package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;
import java.util.LinkedList;
import java.util.List;
import java.util.HashSet;
import java.util.Set;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

public class DotStoreString extends DeltaCRDT implements Serializable {


    public List<Pair<Event,Dot>> context;

    public Set<Dot> store;

    public Set<String> stringset;

    public DotStoreString() {
        context = new LinkedList<>();
        store = new HashSet<>();
       stringset = new HashSet<>();
    }

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

    public int next(int id) {
        //next sequence number
        return this.max(id) + 1;
    }


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
       //     Set<Pair<Event, Dot>> otherStore = p.getKey();
          //  Set<Dot> otherContext = p.getValue();
      //      this.context.addAll(otherContext);
         //   Set<Pair<Event, Dot>> intersection = Sets.intersection(store,otherStore);
           // Set<Pair<Event, Dot>> difference1 = removeDots(store,otherContext);
            //Set<Pair<Event, Dot>> difference2 = removeDots(otherStore,context);
         //   intersection.addAll(difference1);
          //  intersection.addAll(difference2);
         //   store = intersection;


           // System.out.println("current DotStore: "+ this.toString());
        }
    }

/*
    public Set<Pair<Event, Dot>> removeDots(Set<Pair<Event,Dot>> s,Set<Dot> c){
        Set<Pair<Event,Dot>> p = new HashSet<>();
        for(Dot d : c){
            for(Pair pair : s){
                if(pair.getValue().equals(d)){
                 p.add(pair);
                }
            }
        }
        s.removeAll(p);
        return s;
    }

*/
    @Override
    public String toString() {
            String s = "";
            for (String k : stringset){
                s = s + k + ",";
            }
            return s;
    }
}

