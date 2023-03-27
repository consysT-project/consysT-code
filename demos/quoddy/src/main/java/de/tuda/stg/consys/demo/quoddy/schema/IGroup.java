package de.tuda.stg.consys.demo.quoddy.schema;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

public interface IGroup extends Serializable {
    void addPost(Ref<? extends IPost> activity);

    @Transactional
    boolean isUserInGroup(Ref<? extends IUser> user);

    @Transactional
    @StrongOp
    @Strong boolean isOwner(Ref<? extends IUser> user);

    @StrongOp
    @Transactional
    void join(Ref<? extends IUser> user);

    @StrongOp
    @Transactional
    void acceptMembershipRequest(Ref<? extends IUser> user, Ref<? extends IUser> sessionUser);

    @Transactional
    @StrongOp
    void promoteToOwner(Ref<? extends IUser> member);

    @Transactional
    @StrongOp
    void removeOwner(Ref<? extends IUser> user);

    void setName(@Weak @Mutable String name);

    void setDescription(@Weak @Mutable String description);

    @StrongOp
    @Transactional
    void setRequiresJoinConfirmation(@Strong boolean requiresJoinConfirmation);

    @SideEffectFree
    String getId();

    @SideEffectFree
    String getName();

    @SideEffectFree
    String getDescription();

    @SideEffectFree
    @Transactional
    boolean isRequiresJoinConfirmation();

    @SideEffectFree
    @Transactional
    List<Ref<? extends IUser>> getOwners();

    @SideEffectFree
    @Transactional
    List<Ref<? extends IUser>> getMembers();

    @SideEffectFree
    List<Ref<? extends IPost>> getNewestPosts(int n);
}
