package de.tuda.stg.consys.casebenchmarkdist;

import java.io.Serializable;
import java.util.LinkedList;

public class ComChannel implements Serializable {

    LinkedList<String> Queue;

    public void writeIntoQueue(String content){
        Queue.add(content);
    }

    public String popFromQueue(){
        return Queue.pop();
    }

    public int queueLength(){
        return Queue.size();
    }
}
