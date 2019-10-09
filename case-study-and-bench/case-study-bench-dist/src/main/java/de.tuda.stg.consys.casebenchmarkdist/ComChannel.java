package de.tuda.stg.consys.casebenchmarkdist;

import java.io.Serializable;
import java.util.LinkedList;

public class ComChannel implements Serializable {

    //TODO: Stop pop from crashing program when empty.

    LinkedList<String> ToServerQueue;

    LinkedList<String> ToBenchQueue;

    public ComChannel(){
        ToServerQueue = new LinkedList<>();
        ToBenchQueue = new LinkedList<>();
    }

    public void writeToServerQueue(String content){
        ToServerQueue.add(content);
    }

    public String popFromServerQueue(){
        if(ToServerQueue.size()>0)
            return ToServerQueue.pop();
        else return null;
    }

    public int serverQueueLength(){
        return ToServerQueue.size();
    }


    public void writeToBenchQueue(String content){
        ToBenchQueue.add(content);
    }

    public String popFromBenchQueue(){
        if(ToBenchQueue.size()>0)
            return ToBenchQueue.pop();
        else return null;
    }

    public int benchQueueLength(){
        return ToBenchQueue.size();
    }
}
