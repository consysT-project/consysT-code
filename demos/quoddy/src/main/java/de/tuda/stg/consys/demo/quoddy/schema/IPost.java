package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Date;
import java.util.List;
import java.util.UUID;

public interface IPost extends Serializable {
    void addComment(Comment comment);

    @SideEffectFree
    UUID getId();

    @SideEffectFree
    Ref<? extends IUser> getOwner();

    @SideEffectFree
    Date getCreationTimestamp();

    @SideEffectFree
    List<Comment> getComments();
}
