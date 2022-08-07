package de.tuda.stg.consys.demo.quoddy.schema.opcentric;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.demo.quoddy.schema.IGroup;
import de.tuda.stg.consys.demo.quoddy.schema.IPost;
import de.tuda.stg.consys.demo.quoddy.schema.IUser;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.util.*;

public @Mixed class Group implements IGroup {
    private final @Immutable String id;
    private String name;
    private String description;
    private boolean requiresJoinConfirmation;
    private final Map<String, Ref<? extends IUser>> owners;
    private final Map<String, Ref<? extends IUser>> members;
    private final Map<String, Ref<? extends IUser>> pendingMembers;
    private final List<Ref<? extends IPost>> feed;

    public Group() {
        this.id = null;
        this.owners = null;
        this.members = null;
        this.pendingMembers = null;
        this.feed = null;
    }

    @Transactional
    public Group(@Local @Immutable String id, @Weak @Mutable String name, @Weak @Mutable String description,
                 @Strong boolean requiresJoinConfirmation, Ref<User> owner) {
        this.id = id;
        this.name = name;
        this.description = description;
        this.requiresJoinConfirmation = requiresJoinConfirmation; // TODO
        this.owners = new HashMap<>();
        this.owners.put(owner.ref().getId(), owner);
        this.members = new HashMap<>();
        this.pendingMembers = new HashMap<>();
        this.feed = new LinkedList<>();
    }

    public void addPost(Ref<? extends IPost> activity) {
        feed.add(0, activity);
    }

    @Transactional
    public boolean isUserInGroup(Ref<? extends IUser> user) {
        return members.containsKey(user.ref().getId()) || owners.containsKey(user.ref().getId());
    }

    @Transactional
    @StrongOp
    public @Strong boolean isOwner(Ref<? extends IUser> user) {
        return (@Strong boolean) owners.containsKey(user.ref().getId());
    }

    @StrongOp
    @Transactional
    public void join(Ref<? extends IUser> user) {
        if (!requiresJoinConfirmation) {
            members.put(user.ref().getId(), user);
        } else {
            pendingMembers.put(user.ref().getId(), user);
        }
    }

    @StrongOp
    @Transactional
    public void acceptMembershipRequest(Ref<? extends IUser> user, Ref<? extends IUser> sessionUser) {
        if (isOwner(sessionUser)) {
            throw new IllegalArgumentException("user is not privileged to accept membership requests");
        }

        if ((@Strong boolean) (pendingMembers.remove(user.ref().getId()) != null)) {
            members.put(user.ref().getId(), user);
        } else {
            throw new IllegalArgumentException("user has not requested membership");
        }
    }

    @Transactional
    @StrongOp
    public void promoteToOwner(Ref<? extends IUser> member) {
        if ((@Strong boolean) (members.remove(member.ref().getId()) != null)) {
            owners.put(member.ref().getId(), member);
        } else {
            throw new IllegalArgumentException("user is not member of group");
        }
    }

    @Transactional
    @StrongOp
    public void removeOwner(Ref<? extends IUser> user) {
        this.owners.remove(user.ref().getId());
    }

    public void setName(@Weak @Mutable String name) {
        this.name = name;
    }

    public void setDescription(@Weak @Mutable String description) {
        this.description = description;
    }

    @StrongOp
    public void setRequiresJoinConfirmation(@Strong boolean requiresJoinConfirmation) {
        this.requiresJoinConfirmation = requiresJoinConfirmation;
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

    @SideEffectFree
    public boolean isRequiresJoinConfirmation() {
        return requiresJoinConfirmation;
    }

    @SideEffectFree
    public List<Ref<? extends IUser>> getOwners() {
        return new ArrayList<>(owners.values());
    }

    @SideEffectFree
    public List<Ref<? extends IUser>> getMembers() {
        return new ArrayList<>(members.values());
    }

    @SideEffectFree
    public List<Ref<? extends IPost>> getNewestPosts(int n) {
        return (@Weak @Immutable List<Ref<? extends IPost>>) feed.subList(0, Math.min(n, feed.size()));
    }
}
