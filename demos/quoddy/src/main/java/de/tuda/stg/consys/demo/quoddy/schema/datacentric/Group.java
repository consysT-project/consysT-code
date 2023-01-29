package de.tuda.stg.consys.demo.quoddy.schema.datacentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.quoddy.AppException;
import de.tuda.stg.consys.demo.quoddy.schema.IGroup;
import de.tuda.stg.consys.demo.quoddy.schema.IPost;
import de.tuda.stg.consys.demo.quoddy.schema.IUser;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.util.*;

public @Weak class Group implements IGroup {
    private final @Immutable String id;
    private String name;
    private String description;
    private final Ref<@Mutable BoolBox> requiresJoinConfirmation;
    private final Ref<@Mutable RefMap<String, Ref<? extends IUser>>> owners;
    private final Ref<@Mutable RefMap<String, Ref<? extends IUser>>> members;
    private final Ref<@Mutable RefMap<String, Ref<? extends IUser>>> pendingMembers;
    private final List<Ref<? extends IPost>> feed;

    @Transactional
    public Group(@Local @Immutable String id, @Weak @Mutable String name, @Weak @Mutable String description,
                 Ref<@Mutable BoolBox> requiresJoinConfirmation, Ref<User> owner,
                 Ref<@Mutable RefMap<String, Ref<? extends IUser>>> owners,
                 Ref<@Mutable RefMap<String, Ref<? extends IUser>>> members,
                 Ref<@Mutable RefMap<String, Ref<? extends IUser>>> pendingMembers) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.requiresJoinConfirmation = requiresJoinConfirmation; // TODO
        this.owners = owners;
        this.owners.ref().put(owner.ref().getId(), owner);
        this.members = members;
        this.pendingMembers = pendingMembers;
        this.feed = new LinkedList<>();
    }

    public void addPost(Ref<? extends IPost> activity) {
        feed.add(0, activity);
    }

    @Transactional
    public boolean isUserInGroup(Ref<? extends IUser> user) {
        return members.ref().containsKey(user.ref().getId()) || owners.ref().containsKey(user.ref().getId());
    }

    @Transactional
    @StrongOp
    public @Strong boolean isOwner(Ref<? extends IUser> user) {
        return (@Strong boolean) owners.ref().containsKey(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void join(Ref<? extends IUser> user) {
        if (!requiresJoinConfirmation.ref().get()) {
            members.ref().put(user.ref().getId(), user);
        } else {
            pendingMembers.ref().put(user.ref().getId(), user);
        }
    }

    @StrongOp
    @Transactional
    public void acceptMembershipRequest(Ref<? extends IUser> user, Ref<? extends IUser> sessionUser) {
        if (isOwner(sessionUser)) {
            throw new AppException("user is not privileged to accept membership requests");
        }

        if ((@Strong boolean) (pendingMembers.ref().remove(user.ref().getId()) != null)) {
            members.ref().put(user.ref().getId(), user);
        } else {
            throw new AppException("user has not requested membership");
        }
    }

    @Transactional
    @StrongOp
    public void promoteToOwner(Ref<? extends IUser> member) {
        if ((@Strong boolean) (members.ref().remove(member.ref().getId()) != null)) {
            owners.ref().put(member.ref().getId(), member);
        } else {
            throw new AppException("user is not member of group");
        }
    }

    @Transactional
    @StrongOp
    public void removeOwner(Ref<? extends IUser> user) {
        this.owners.ref().remove(user.ref().getId());
    }

    public void setName(@Weak @Mutable String name) {
        this.name = name;
    }

    public void setDescription(@Weak @Mutable String description) {
        this.description = description;
    }

    @StrongOp @Transactional
    public void setRequiresJoinConfirmation(@Strong boolean requiresJoinConfirmation) {
        this.requiresJoinConfirmation.ref().set(requiresJoinConfirmation);
    }

    @SideEffectFree
    public String getId() {
        return id;
    }

    @SideEffectFree
    public String getName() {
        return name;
    }

    @SideEffectFree
    public String getDescription() {
        return description;
    }

    @SideEffectFree @Transactional
    public boolean isRequiresJoinConfirmation() {
        return requiresJoinConfirmation.ref().get();
    }

    @SideEffectFree @Transactional
    public List<Ref<? extends IUser>> getOwners() {
        return new ArrayList<>(owners.ref().values());
    }

    @SideEffectFree @Transactional
    public List<Ref<? extends IUser>> getMembers() {
        return new ArrayList<>(members.ref().values());
    }

    @SideEffectFree
    public List<Ref<? extends IPost>> getNewestPosts(int n) {
        return (@Weak @Immutable List<Ref<? extends IPost>>) feed.subList(0, Math.min(n, feed.size()));
    }
}
