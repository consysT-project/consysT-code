package de.tuda.stg.consys.demo.docshare.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

public class User implements Serializable {

    private String name = "";


    public User() {}

    public User(@Weak String name) {
        this.name = name;
    }

    @Transactional
    public void editDocumentContent(Ref<@Mutable Document> document, @Strong String content) {
        document.ref().setContent(content);
    }

    @Transactional
    public void editDocumentDescription(Ref<@Mutable Document> document, @Weak String description) {
        document.ref().setDescription(description);
    }

}
