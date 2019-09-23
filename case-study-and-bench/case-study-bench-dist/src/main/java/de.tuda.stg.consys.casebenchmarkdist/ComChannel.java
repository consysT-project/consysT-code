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
        return ToServerQueue.pop();
    }

    public int serverQueueLength(){
        return ToServerQueue.size();
    }


    public void writeToBenchQueue(String content){
        ToBenchQueue.add(content);
    }

    public String popFromBenchQueue(){
        return ToBenchQueue.pop();
    }

    public int benchQueueLength(){
        return ToBenchQueue.size();
    }
}
