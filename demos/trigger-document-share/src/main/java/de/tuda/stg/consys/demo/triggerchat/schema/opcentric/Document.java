package de.tuda.stg.consys.demo.triggerchat.schema.opcentric;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.Triggerable;
import de.tuda.stg.consys.demo.triggerchat.Session;
import de.tuda.stg.consys.demo.triggerchat.extras.ConnectionManager;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public @Mixed class Document implements Serializable, Triggerable {

    private String title;

    private String content;

    private String description;

    public Document() {}

    public Document(@Local @Mutable String title) {
        this.title = title;
        this.content = "";
        this.description = "";
    }

    @WeakOp @SideEffectFree
    public String getTitle() {
        return this.title;
    }

    @StrongOp @SideEffectFree
    public String getContent() {
        return this.content;
    }

    @WeakOp @SideEffectFree
    public String getDescription() {
        return this.description;
    }

    @StrongOp
    public void setContent(String content) {
        this.content = content;
    }

    @WeakOp
    public void setDescription(String description) {
        this.description = description;
    }

    @Override
    public void onTrigger() {
        ConnectionManager.trigger();
    }
}
