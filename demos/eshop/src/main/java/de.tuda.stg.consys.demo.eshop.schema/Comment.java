package de.tuda.stg.consys.demo.eshop.schema;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;

public class Comment implements Serializable {
    private JRef<User> author;

    private String content;

    Comment(String content, JRef<User> author){
        this.author = author;
        this.content = content;
    }

    public String getContent(){
        return content;
    }

    public String getAuthor(){
        return author.ref().getName();
    }


}
