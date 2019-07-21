package de.tuda.stg.consys.casestudy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;

public class Comment implements Serializable {
    private JRef<@Strong User> author;

    private String content;

    Comment(String content, JRef<@Strong User> author){
        this.author = author;
        this.content = content;
    }

    public String getContent(){
        return content;
    }

    public String getAuthor(){
        return author.invoke("getName");
    }

    public boolean editContent(String newContent, JReplicaSystem system){
        if(author.invoke("verifyLogin", system)){
            this.content = newContent;
            return true;
        }
        return false;
    }

}
