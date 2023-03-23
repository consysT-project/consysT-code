package de.tuda.stg.consys.demo.triggerchat.schema.opcentric;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.Triggerable;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public @Mixed class Document implements Serializable {

    private String title;

    private String content;

    public Document() {}

    public Document(@Local @Mutable String title) {
        this.title = title;
        this.content = "";
    }

    @WeakOp @SideEffectFree
    public String getTitle() {
        return this.title;
    }

    @WeakOp @SideEffectFree
    public String getContent() {
        return this.content;
    }

    @StrongOp
    public void save(String content) {
        this.content = content;
    }

}
