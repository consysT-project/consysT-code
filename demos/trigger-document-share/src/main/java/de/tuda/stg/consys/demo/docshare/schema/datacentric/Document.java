package de.tuda.stg.consys.demo.docshare.schema.datacentric;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.Triggerable;
import de.tuda.stg.consys.demo.docshare.extras.ConnectionManager;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

public class Document implements Serializable, Triggerable {

    private String title;

    private String content;

    private String description;

    public Document() {}

    public Document(@Local @Mutable String title) {
        this.title = title;
        this.content = "";
        this.description = "";
    }

    @SideEffectFree
    public String getTitle() {
        return this.title;
    }

    @SideEffectFree
    public String getContent() {
        return this.content;
    }

    @SideEffectFree
    public String getDescription() {
        return this.description;
    }

    public void setContent(String content) {
        this.content = content;
    }

    public void setDescription(String description) {
        this.description = description;
    }

    @Override
    public void onTrigger() {
        ConnectionManager.trigger();
    }
}
